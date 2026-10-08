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


variable {SI : Type _} [Iris.SIdx SI]

namespace Iris

section prod

open BI Iris.Std BIBase.BiEntails

@[rocq_alias prod_validI]
theorem prod_validI [Sbi SI PROP] [ORA SI A] [ORA SI B] (x : A × B) :
    ✓[SI] x ⊣⊢@{PROP} ✓[SI] x.1 ∧ ✓[SI] x.2 := by
  sbi_unfold; intro _; exact .rfl

theorem prod_ordI [Sbi SI PROP] [ORA SI A] [ORA SI B] (x y : A × B) :
    x ≼ₒ[SI] y ⊣⊢@{PROP} x.1 ≼ₒ[SI] y.1 ∧ x.2 ≼ₒ[SI] y.2 := by
  sbi_unfold; intro _; exact Prod.ordN_def

@[rocq_alias prod_includedI]
theorem prod_includedI [Sbi SI PROP] [ORA SI A] [ORA SI B] (x y : A × B) :
    x ≼[SI] y ⊣⊢@{PROP} x.1 ≼[SI] y.1 ∧ x.2 ≼[SI] y.2 := by
  sbi_unfold; intro _; exact Prod.incN_def

end prod

section option

open BI Iris.Std BIBase.BiEntails

@[rocq_alias option_validI]
theorem option_validI [Sbi SI PROP] [ORA SI A] {mx : Option A} :
  ✓[SI] mx ⊣⊢@{PROP} mx.elim iprop(True) (internalCmraValid (SI := SI)) := by
  cases mx <;> simp only [Option.elim] <;> sbi_unfold <;> intro _ <;> exact .rfl

theorem option_ordI [Sbi SI PROP] [ORA SI A] {mx my : Option A} :
  mx ≼ₒ[SI] my ⊣⊢@{PROP}
    mx.elim (my.elim iprop(True) fun y => iprop(⌜Increasing SI y⌝))
      fun x => my.elim iprop(False) fun y => iprop((x ≼ₒ[SI] y) ∨ (x ≡[SI] y)) := by
  rcases mx with _ | x <;> rcases my with _ | y
  · exact internalCmraOrder_pure fun _ => iff_true_intro trivial
  · exact internalCmraOrder_pure fun _ => Option.none_ordN_some_iff
  · exact internalCmraOrder_pure fun _ => iff_false_intro Option.not_some_ordN_none
  · simp only [Option.elim]; sbi_unfold; intro _; exact Option.some_ordN_some_iff.trans Or.comm

@[rocq_alias option_includedI]
theorem option_includedI [Sbi SI PROP] [ORA SI A] {mx my : Option A} :
  mx ≼[SI] my ⊣⊢@{PROP}
    mx.elim iprop(True) fun x => my.elim iprop(False) fun y => iprop((x ≼[SI] y) ∨ (x ≡[SI] y)) := by
  rcases mx with _ | x <;> rcases my with _ | y <;>
    try exact internalCmraIncluded_pure fun _ => by simp [Option.incN_iff]
  simp only [Option.elim]; sbi_unfold; intro _; exact Option.some_incN_some_iff.trans Or.comm

theorem option_ord_totalI [Sbi SI PROP] [ORA SI A] [IncOrd SI A] [OrderRefl SI A] {mx my : Option A} :
  mx ≼ₒ[SI] my ⊣⊢@{PROP}
    mx.elim iprop(True) fun x => my.elim iprop(False) fun y => iprop(x ≼ₒ[SI] y) := by
  rcases mx with _ | x <;> rcases my with _ | y <;>
    first
    | exact internalCmraOrder_iff fun _ => by simp [Option.ordN_iff_orderRefl]
    | exact internalCmraOrder_pure fun _ => by simp [Option.ordN_iff_orderRefl]

@[rocq_alias option_included_totalI]
theorem option_included_totalI [Sbi SI PROP] [ORA SI A] [IsTotal A] {mx my : Option A} :
  mx ≼[SI] my ⊣⊢@{PROP}
    mx.elim iprop(True) fun x => my.elim iprop(False) fun y => iprop(x ≼[SI] y) := by
  rcases mx with _ | x <;> rcases my with _ | y <;>
    first
    | exact internalCmraIncluded_iff fun _ => by simp [Option.incN_iff_is_total]
    | exact internalCmraIncluded_pure fun _ => by simp [Option.incN_iff_is_total]

@[rocq_alias Some_included_totalI]
theorem Some_included_totalI [Sbi SI PROP] [ORA SI A] [IsTotal A] {x y : A} :
    some x ≼[SI] some y ⊣⊢@{PROP} x ≼[SI] y :=
  option_included_totalI

theorem some_ordI [Sbi SI PROP] [ORA SI A] [OrderRefl SI A] {x y : A} :
    some x ≼ₒ[SI] some y ⊣⊢@{PROP} x ≼ₒ[SI] y :=
  internalCmraOrder_iff fun _ => Option.some_ordN_some_iff_orderRefl

theorem some_ordI_none [Sbi SI PROP] [ORA SI A] {x : A} : some x ≼ₒ[SI] none ⊢@{PROP} False :=
  (internalCmraOrder_pure fun _ => iff_false_intro Option.not_some_ordN_none).mp.trans
    (pure_elim' False.elim)

end option

section heap_view

open HeapView BI Iris.Std PartialMap LawfulPartialMap BIBase.BiEntails

variable {F K V : Type _} {H : Type _ → Type _}
variable [LawfulPartialMap H K] [ORA SI V]

theorem auth_op_frag_validI_ord [Sbi SI PROP] [IncOrd SI V] (dp : DFrac) (m : H V) k dq v :
  ✓[SI] (Auth (SI := SI) dp m • Frag k dq v) ⊣⊢@{PROP}
    ∃ v' dq', ⌜✓[SI] dp⌝ ∧ ⌜get? m k = .some v'⌝ ∧ ✓[SI] (dq', v') ∧
      some (dq, v) ≼ₒ[SI] some (dq', v') := by
  sbi_unfold; intro _; exact auth_op_frag_validN_iff_ord

@[rocq_alias gmap_view_both_dfrac_validI]
theorem auth_op_frag_validI [Sbi SI PROP] [OrdInc SI V] (dp : DFrac) (m : H V) k dq v :
  ✓[SI] (Auth (SI := SI) dp m • Frag k dq v) ⊣⊢@{PROP}
    ∃ v' dq', ⌜✓[SI] dp⌝ ∧ ⌜get? m k = .some v'⌝ ∧ ✓[SI] (dq', v') ∧
      some (dq, v) ≼[SI] some (dq', v') := by
  sbi_unfold; intro _; exact auth_op_frag_validN_iff

@[rocq_alias gmap_view_both_validI]
theorem auth_op_frag_one_validI [Sbi SI PROP] (dp : DFrac) (m : H V) k v :
  ✓[SI] (Auth (SI := SI) dp m • Frag k (.own One.one) v) ⊣⊢@{PROP}
    ⌜✓[SI] dp⌝ ∧ ✓[SI] v ∧ get? m k ≡[SI] .some v := by
  sbi_unfold; intro _; exact auth_op_frag_one_validN_iff

theorem auth_op_frag_validI_total_ord [Sbi SI PROP] [OrderRefl SI V] [IncOrd SI V] (dp : DFrac) (m : H V)
    k dq v :
  ✓[SI] (Auth (SI := SI) dp m • Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓[SI] dp⌝ ∧ ⌜✓[SI] dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      ✓[SI] v' ∧ v ≼ₒ[SI] v' := by
  sbi_unfold; intro _; exact auth_op_frag_validN_total_iff_ord

@[rocq_alias gmap_view_both_validI_total]
theorem auth_op_frag_validI_total [Sbi SI PROP] [OrderRefl SI V] [OrdInc SI V] (dp : DFrac) (m : H V)
    k dq v :
  ✓[SI] (Auth (SI := SI) dp m • Frag k dq v) ⊢@{PROP}
    ∃ v', ⌜✓[SI] dp⌝ ∧ ⌜✓[SI] dq⌝ ∧ ⌜get? m k = .some v'⌝ ∧
      ✓[SI] v' ∧ v ≼[SI] v' := by
  sbi_unfold; intro _; exact auth_op_frag_validN_total_iff

@[rocq_alias gmap_view_frag_op_validI]
theorem frag_op_frag_validI [Sbi SI PROP] k dq1 dq2 v1 v2 :
  ✓[SI] (Frag (H := H) (V := V) k dq1 v1 • Frag (SI := SI) k dq2 v2) ⊣⊢@{PROP}
    ⌜✓[SI] (dq1 • dq2)⌝ ∧ ✓[SI] (v1 • v2) := by
  sbi_unfold; intro _; exact frag_op_validN_iff

end heap_view

section agree_inclusion

open Iris BI Agree OFE

variable [Sbi SI PROP] [OFE SI A]

@[rocq_alias agree_equivI]
theorem agree_equivI {a b : A} : toAgree a ≡[SI] toAgree b ⊣⊢@{PROP} a ≡[SI] b := by
  sbi_unfold; intro _; exact ⟨Agree.toAgree_injN, (NonExpansive.ne ·)⟩

@[rocq_alias agree_op_invI]
theorem agree_op_invI {x y : Agree A} : ✓[SI] (x • y) ⊢@{PROP} x ≡[SI] y :=
  siPure_mono (fun _ => op_invN)

@[rocq_alias to_agree_validI]
theorem toAgree_validI (a : A) :
    ⊢@{PROP} ✓[SI] (toAgree a) :=
  internalCmraValid_intro fun _ => by simp

@[rocq_alias to_agree_op_validI]
theorem toAgree_op_validI (a b : A) :
    ✓[SI] (toAgree a • toAgree b) ⊣⊢@{PROP} a ≡[SI] b := by
  sbi_unfold; intro _; exact toAgree_op_validN_iff_dist

@[rocq_alias to_agree_uninjI]
theorem toAgree_uninjI (x : Agree A) :
    ✓[SI] x ⊢@{PROP} ∃ a, toAgree a ≡[SI] x := by
  sbi_unfold; intro _; exact fun h => toAgree_uninjN h

@[rocq_alias agree_op_equiv_to_agreeI]
theorem agree_op_equiv_toAgreeI (x y : Agree A) (a : A) :
    x • y ≡[SI] toAgree a ⊢@{PROP} x ≡[SI] y ∧ y ≡[SI] toAgree a := by
  sbi_unfold; intro _ h
  have hxy := op_invN (h.validN.mpr toAgree_validN)
  exact ⟨hxy, ((Dist.of_eq idemp).symm.trans hxy.symm.op_l).trans h⟩

theorem agree_ordI (x y : Agree A) :
    x ≼ₒ[SI] y ⊣⊢@{PROP} y ≡[SI] x • y := by
  sbi_unfold; intro _
  exact ordN.trans ⟨(·.trans op_commN), (·.trans op_commN)⟩

@[rocq_alias agree_includedI]
theorem agree_includedI (x y : Agree A) :
    x ≼[SI] y ⊣⊢@{PROP} y ≡[SI] x • y :=
  internalCmraIncluded_iff_internalCmraOrder.trans (agree_ordI x y)

theorem toAgree_ordI (a b : A) :
    toAgree a ≼ₒ[SI] toAgree b ⊣⊢@{PROP} a ≡[SI] b := by
  sbi_unfold; intro _; exact toAgree_ordN

@[rocq_alias to_agree_includedI]
theorem toAgree_includedI (a b : A) :
    toAgree a ≼[SI] toAgree b ⊣⊢@{PROP} a ≡[SI] b :=
  internalCmraIncluded_iff_internalCmraOrder.trans (toAgree_ordI a b)

end agree_inclusion

section auth
open Iris BI Auth

variable [Sbi SI PROP] [UORA SI A]

@[rocq_alias auth_auth_dfrac_validI]
theorem auth_dfrac_validI (dq : DFrac) (a : A) :
    ✓[SI] (●{dq} a : Auth (SI := SI) A) ⊣⊢@{PROP} ⌜✓[SI] dq⌝ ∧ ✓[SI] a := by
  sbi_unfold; intro _; exact auth_dfrac_validN

@[rocq_alias auth_auth_validI]
theorem auth_validI (a : A) : ✓[SI] (● a : Auth (SI := SI) A) ⊣⊢@{PROP} ✓[SI] a := by
  sbi_unfold; intro _; exact auth_validN

@[rocq_alias auth_auth_dfrac_op_validI]
theorem auth_dfrac_op_validI (dq1 dq2 : DFrac) (a1 a2 : A) :
    ✓[SI] ((●{dq1} a1 : Auth (SI := SI) A) • (●{dq2} a2)) ⊣⊢@{PROP}
      ⌜✓[SI] (dq1 • dq2)⌝ ∧ a1 ≡[SI] a2 ∧ ✓[SI] a1 := by
  sbi_unfold; intro _; exact auth_dfrac_op_validN

@[rocq_alias auth_frag_validI]
theorem frag_validI (a : A) :
    ✓[SI] (◯ a : Auth (SI := SI) A) ⊣⊢@{PROP} ✓[SI] a := by
  sbi_unfold; intro _; exact frag_validN

theorem both_dfrac_validI_ord [IncOrd SI A] (dq : DFrac) (a b : A) :
    ✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b) ⊣⊢@{PROP}
    ⌜✓[SI] dq⌝ ∧ b ≼ₒ[SI] a ∧ ✓[SI] a := by
  sbi_unfold; intro _; exact both_dfrac_validN_ord

@[rocq_alias auth_both_dfrac_validI]
theorem both_dfrac_validI [OrdInc SI A] (dq : DFrac) (a b : A) :
    ✓[SI] ((●{dq} a : Auth (SI := SI) A) • ◯ b) ⊣⊢@{PROP}
    ⌜✓[SI] dq⌝ ∧ b ≼[SI] a ∧ ✓[SI] a := by
  sbi_unfold; intro _; exact both_dfrac_validN

theorem auth_both_validI_ord [IncOrd SI A] (a b : A) :
    ✓[SI] ((● a : Auth (SI := SI) A) • ◯ b) ⊣⊢@{PROP}
      b ≼ₒ[SI] a ∧ ✓[SI] a := by
  sbi_unfold; intro _; exact both_validN_ord

@[rocq_alias auth_both_validI]
theorem auth_both_validI [OrdInc SI A] (a b : A) :
    ✓[SI] ((● a : Auth (SI := SI) A) • ◯ b) ⊣⊢@{PROP}
      b ≼[SI] a ∧ ✓[SI] a := by
  sbi_unfold; intro _; exact both_validN

end auth

section dfrac_agree
variable [Sbi SI PROP] {A : Type _} [OFE SI A]

open BI

@[rocq_alias dfrac_agree_validI]
theorem dfrac_agree_validI (dq : DFrac) (x : A) :
    ✓[SI] (DFracAgree.mk (SI := SI) dq x) ⊣⊢@{PROP} ⌜✓[SI] dq⌝ := by
  sbi_unfold; intro _; exact ⟨fun h => h.1, fun h => ⟨h, by simp [DFracAgree.mk]⟩⟩

@[rocq_alias dfrac_agree_validI_2]
theorem dfrac_agree_validI_2 (dq1 dq2 : DFrac) (x y : A) :
    ✓[SI] (DFracAgree.mk (SI := SI) dq1 x • DFracAgree.mk dq2 y) ⊣⊢@{PROP}
      ⌜✓[SI] (dq1 • dq2)⌝ ∧ x ≡[SI] y :=
  (prod_validI _).trans (and_congr internalCmraValid_discrete (toAgree_op_validI x y))

end dfrac_agree

section generic
open BI ORA OFE
variable [Sbi SI PROP]

@[rocq_alias ucmra_unit_validI]
theorem ucmra_unit_validI [UORA SI A] : ⊢@{PROP} ✓[SI] (unit : A) := internalCmraValid_intro unit_valid

@[rocq_alias cmra_validI_op_r]
theorem cmra_validI_op_r [ORA SI A] (x y : A) : ✓[SI] (x • y) ⊢@{PROP} ✓[SI] y :=
  siPure_mono fun _ => validN_op_right

@[rocq_alias cmra_validI_op_l]
theorem cmra_validI_op_l [ORA SI A] (x y : A) : ✓[SI] (x • y) ⊢@{PROP} ✓[SI] x :=
  siPure_mono fun _ => validN_op_l

@[rocq_alias cmra_morphism_validI]
theorem cmra_morphism_validI [ORA SI A] [ORA SI B] (f : A -C>[SI] B) (x : A) :
    ✓[SI] x ⊢@{PROP} ✓[SI] (f x) :=
  siPure_mono fun _ => f.validN

@[rocq_alias f_homom_includedI]
theorem f_homom_includedI [ORA SI A] [ORA SI B] (x y : A) (f : A → B) [NonExpansive SI f]
    (Hf : ∀ c (n : SI), f x • f c ≡{n}≡ f (x • c)) :
    x ≼[SI] y ⊢@{PROP} f x ≼[SI] f y :=
  siPure_mono <| BI.exists_elim fun c => BI.exists_intro_trans (f c) <|
    internalEq_entails.mpr fun n heq => (NonExpansive.ne heq).trans (Hf c n).symm

@[rocq_alias id_freeI_r]
theorem id_freeI_r [ORA SI A] (x y : A) [IdFree SI x] :
    ⊢@{PROP} ✓[SI] x -∗ (x • y) ≡[SI] x -∗ False := by
  have H : iprop((x • y) ≡[SI] x ∗ ✓[SI] x) ⊢@{PROP} False := by
    refine siPure_and_sep.mpr.trans ?_; sbi_unfold; intro _; exact fun h => id_freeN_r h.2 h.1
  exact wand_intro_left (wand_intro_left ((sep_mono_right sep_emp.mp).trans H))

@[rocq_alias id_freeI_l]
theorem id_freeI_l [ORA SI A] (x y : A) [IdFree SI x] :
    ⊢@{PROP} ✓[SI] x -∗ (y • x) ≡[SI] x -∗ False := by
  have H : iprop((y • x) ≡[SI] x ∗ ✓[SI] x) ⊢@{PROP} False := by
    refine siPure_and_sep.mpr.trans ?_; sbi_unfold; intro _; exact fun h => id_freeN_l h.2 h.1
  exact wand_intro_left (wand_intro_left ((sep_mono_right sep_emp.mp).trans H))

@[rocq_alias cmra_later_opI]
theorem cmra_later_opI [SIdxFinite SI] [ORA SI A] (x y1 y2 : A) :
    ▷ (✓[SI] x ∧ x ≡[SI] y1 • y2) ⊢@{PROP}
      ◇ ∃ z1 z2, x ≡[SI] z1 • z2 ∧ ▷ (z1 ≡[SI] y1) ∧ ▷ (z2 ≡[SI] y2) := by
  unfold BIBase.except0; sbi_unfold; intro n h
  rcases SIdxFinite.finite_index n with rfl | ⟨m, rfl⟩
  · exact .inl fun _ hm => (SIdx.not_lt_zero _ hm).elim
  · have ⟨hv, he⟩ := h m (SIdx.lt_succ_self m)
    have ⟨z1, z2, hx, hz1, hz2⟩ := extend' hv he
    exact .inr ⟨z1, z2, Dist.of_eq hx, fun _ hk => hz1.le (SIdx.lt_succ_r.mp hk),
      fun _ hk => hz2.le (SIdx.lt_succ_r.mp hk)⟩

@[rocq_alias cmra_later_opI_total]
theorem cmra_later_opI_total [SIdxFinite SI] [ORA SI A] [IsTotal A] (x y1 y2 : A) :
    ▷ (✓[SI] x ∧ x ≡[SI] y1 • y2) ⊢@{PROP}
      ∃ z1 z2, x ≡[SI] z1 • z2 ∧ ▷ (z1 ≡[SI] y1) ∧ ▷ (z2 ≡[SI] y2) := by
  sbi_unfold; intro n h
  rcases SIdxFinite.finite_index n with rfl | ⟨m, rfl⟩
  · exact ⟨x, core x, (op_core_dist x).symm, fun _ hm => (SIdx.not_lt_zero _ hm).elim,
      fun _ hm => (SIdx.not_lt_zero _ hm).elim⟩
  · have ⟨hv, he⟩ := h m (SIdx.lt_succ_self m)
    have ⟨z1, z2, hx, hz1, hz2⟩ := extend' hv he
    exact ⟨z1, z2, Dist.of_eq hx, fun _ hk => hz1.le (SIdx.lt_succ_r.mp hk),
      fun _ hk => hz2.le (SIdx.lt_succ_r.mp hk)⟩

end generic

section discrete_fun
open BI ORA
variable [Sbi SI PROP]

@[rocq_alias discrete_fun_validI]
theorem discrete_fun_validI {ι : Type _} {β : ι → Type _} [∀ i, UORA SI (β i)]
    (g : ∀ i, β i) : ✓[SI] g ⊣⊢@{PROP} ∀ i, ✓[SI] (g i) := by
  sbi_unfold; intro _; exact .rfl

end discrete_fun

section excl
open BI Excl OFE
variable [Sbi SI PROP] [OFE SI A]

@[rocq_alias algebra.excl_equivI]
theorem excl_equivI (x y : Excl A) :
    x ≡[SI] y ⊣⊢@{PROP}
      match x, y with
      | excl a, excl b => iprop(a ≡[SI] b)
      | invalid, invalid => iprop(True)
      | _, _ => iprop(False) := by
  cases x <;> cases y <;> sbi_unfold <;> intro _ <;> exact .rfl

@[rocq_alias excl_validI]
theorem excl_validI (x : Excl A) :
    ✓[SI] x ⊣⊢@{PROP} ⌜x ≠ Excl.invalid⌝ := by
  sbi_unfold; intro _
  cases x with
  | excl a => exact ⟨fun _ => nofun, fun _ => trivial⟩
  | invalid => exact ⟨fun h => h.elim, fun h => (h rfl).elim⟩

theorem excl_ordI (x y : Excl A) :
    x ≼ₒ[SI] y ⊣⊢@{PROP} ⌜y = Excl.invalid⌝ :=
  internalCmraOrder_pure ordN_iff

@[rocq_alias excl_includedI]
theorem excl_includedI (x y : Excl A) :
    x ≼[SI] y ⊣⊢@{PROP} ⌜y = Excl.invalid⌝ :=
  internalCmraIncluded_pure ordN_iff

end excl

section csum
open BI Csum OFE ORA
variable [Sbi SI PROP]

@[rocq_alias algebra.csum_equivI]
theorem csum_equivI [OFE SI A] [OFE SI B] (x y : Csum A B) :
    x ≡[SI] y ⊣⊢@{PROP}
      match x, y with
      | inl a, inl b => iprop(a ≡[SI] b)
      | inr a, inr b => iprop(a ≡[SI] b)
      | invalid, invalid => iprop(⌜True⌝)
      | _, _ => iprop(⌜False⌝) :=
  BI.csum_equivI x y

@[rocq_alias csum_validI]
theorem csum_validI [ORA SI A] [ORA SI B] (x : Csum A B) : ✓[SI] x ⊣⊢@{PROP} match x with
      | inl a => iprop(✓[SI] a)
      | inr b => iprop(✓[SI] b)
      | invalid => iprop(False) := by
  cases x <;> sbi_unfold <;> intro _ <;> exact .rfl

theorem csum_ordI [ORA SI A] [ORA SI B] (x y : Csum A B) : x ≼ₒ[SI] y ⊣⊢@{PROP} match x, y with
      | inl a, inl b => iprop(a ≼ₒ[SI] b)
      | inr a, inr b => iprop(a ≼ₒ[SI] b)
      | _, invalid => iprop(True)
      | _, _ => iprop(False) := by
  cases x <;> cases y <;>
    first
    | exact internalCmraOrder_iff fun _ => by simp [Csum.ordN]
    | exact internalCmraOrder_pure fun _ => by simp [Csum.ordN]

@[rocq_alias csum_includedI]
theorem csum_includedI [ORA SI A] [ORA SI B] (x y : Csum A B) : x ≼[SI] y ⊣⊢@{PROP} match x, y with
      | inl a, inl b => iprop(a ≼[SI] b)
      | inr a, inr b => iprop(a ≼[SI] b)
      | _, invalid => iprop(True)
      | _, _ => iprop(False) := by
  cases x <;> cases y <;>
    first
    | exact internalCmraIncluded_iff fun _ => by simp [Csum.includedN]
    | exact internalCmraIncluded_pure fun _ => by simp [Csum.includedN]

end csum

section list
open BI OFE
variable [Sbi SI PROP] [OFE SI A]

@[rocq_alias list_equivI]
theorem list_equivI (l1 l2 : List A) :
    l1 ≡[SI] l2 ⊣⊢@{PROP} ∀ (i : Nat), (l1[i]? : Option A) ≡[SI] (l2[i]? : Option A) := by
  sbi_unfold; intro _; exact list_dist_lookup

end list

section heap
open BI ORA Iris.Std PartialMap
variable [Sbi SI PROP] {M : Type _ → Type _} {K : Type _} [LawfulPartialMap M K]

@[rocq_alias gmap_equivI]
theorem heap_equivI [OFE SI V] (m1 m2 : M V) :
    m1 ≡[SI] m2 ⊣⊢@{PROP} ∀ i, get? m1 i ≡[SI] get? m2 i := by
  sbi_unfold; intro _; exact .rfl

@[rocq_alias gmap_validI]
theorem heap_validI [ORA SI V] (m : M V) :
    ✓[SI] m ⊣⊢@{PROP} ∀ i, ✓[SI] (get? m i) := by
  sbi_unfold; intro _; exact .rfl

@[rocq_alias singleton_validI]
theorem singleton_validI [ORA SI V] (i : K) (x : V) :
    ✓[SI] (PartialMap.singleton i x : M V) ⊣⊢@{PROP} ✓[SI] x := by
  sbi_unfold; intro _; exact Heap.singleton_validN_iff

@[rocq_alias gmap_union_equiv_eqI]
theorem heap_union_equiv_eqI [OFE SI V] (m m1 m2 : M V) :
    m ≡[SI] m1 ∪ m2 ⊣⊢@{PROP}
      ∃ m1' m2', ⌜m = m1' ∪ m2'⌝ ∧ m1' ≡[SI] m1 ∧ m2' ≡[SI] m2 := by
  sbi_unfold; intro _; exact _root_.PartialMap.union_dist_iff

end heap

section view
open BI ORA View ViewRel IsViewRel
variable [Sbi SI PROP] [OFE SI A] [UORA SI B] {R : ViewRel SI A B} [IsViewRel R]

@[rocq_alias view_both_dfrac_validI_1]
theorem view_both_dfrac_validI_1 (relI : SiProp SI) (dq : DFrac) (a : A) (b : B)
    (H : ∀ (n : SI), R n a b → relI.holds n) :
    ✓[SI] ((●V{dq} a : View R) • ◯V b) ⊢@{PROP} ⌜✓[SI] dq⌝ ∧ <si_pure> relI := by
  sbi_unfold; intro _
  exact fun hn => ⟨(auth_op_frag_validN_iff.mp hn).1, H _ (auth_op_frag_validN_iff.mp hn).2⟩

@[rocq_alias view_both_dfrac_validI_2]
theorem view_both_dfrac_validI_2 (relI : SiProp SI) (dq : DFrac) (a : A) (b : B)
    (H : ∀ (n : SI), relI.holds n → R n a b) :
    ⌜✓[SI] dq⌝ ∧ <si_pure> relI ⊢@{PROP} ✓[SI] ((●V{dq} a : View R) • ◯V b) := by
  sbi_unfold; intro _; exact fun hn => auth_op_frag_validN_iff.mpr ⟨hn.1, H _ hn.2⟩

@[rocq_alias view_both_dfrac_validI]
theorem view_both_dfrac_validI (relI : SiProp SI) (dq : DFrac) (a : A) (b : B)
    (H : ∀ (n : SI), R n a b ↔ relI.holds n) :
    ✓[SI] ((●V{dq} a : View R) • ◯V b) ⊣⊢@{PROP} ⌜✓[SI] dq⌝ ∧ <si_pure> relI :=
  ⟨view_both_dfrac_validI_1 relI dq a b (fun n => (H n).mp),
   view_both_dfrac_validI_2 relI dq a b (fun n => (H n).mpr)⟩

@[rocq_alias view_both_validI_1]
theorem view_both_validI_1 (relI : SiProp SI) (a : A) (b : B)
    (H : ∀ (n : SI), R n a b → relI.holds n) :
    ✓[SI] ((●V a : View R) • ◯V b) ⊢@{PROP} <si_pure> relI :=
  siPure_mono fun n hn => H n (auth_one_op_frag_validN_iff.mp hn)

@[rocq_alias view_both_validI_2]
theorem view_both_validI_2 (relI : SiProp SI) (a : A) (b : B)
    (H : ∀ (n : SI), relI.holds n → R n a b) :
    <si_pure> relI ⊢@{PROP} ✓[SI] ((●V a : View R) • ◯V b) :=
  siPure_mono fun n hn => auth_one_op_frag_validN_iff.mpr (H n hn)

@[rocq_alias view_both_validI]
theorem view_both_validI (relI : SiProp SI) (a : A) (b : B)
    (H : ∀ (n : SI), R n a b ↔ relI.holds n) :
    ✓[SI] ((●V a : View R) • ◯V b) ⊣⊢@{PROP} <si_pure> relI :=
  ⟨view_both_validI_1 relI a b (fun n => (H n).mp),
   view_both_validI_2 relI a b (fun n => (H n).mpr)⟩

@[rocq_alias view_auth_dfrac_validI]
theorem view_auth_dfrac_validI (relI : SiProp SI) (dq : DFrac) (a : A)
    (H : ∀ (n : SI), relI.holds n ↔ R n a unit) :
    ✓[SI] (●V{dq} a : View R) ⊣⊢@{PROP} ⌜✓[SI] dq⌝ ∧ <si_pure> relI := by
  sbi_unfold; intro _
  exact ⟨fun hn => ⟨(auth_validN_iff.mp hn).1, (H _).mpr (auth_validN_iff.mp hn).2⟩,
    fun hn => auth_validN_iff.mpr ⟨hn.1, (H _).mp hn.2⟩⟩

@[rocq_alias view_auth_validI]
theorem view_auth_validI (relI : SiProp SI) (a : A)
    (H : ∀ (n : SI), relI.holds n ↔ R n a unit) :
    ✓[SI] (●V a : View R) ⊣⊢@{PROP} <si_pure> relI :=
  ⟨siPure_mono fun n hn => (H n).mpr ((auth_one_validN_iff n a).mp hn),
   siPure_mono fun n hn => (auth_one_validN_iff n a).mpr ((H n).mp hn)⟩

@[rocq_alias view_frag_validI]
theorem view_frag_validI (relI : SiProp SI) (b : B)
    (H : ∀ (n : SI), relI.holds n ↔ ∃ a, R n a b) :
    ✓[SI] (◯V b : View R) ⊣⊢@{PROP} <si_pure> relI :=
  ⟨siPure_mono fun n hn => (H n).mpr (frag_validN_iff.mp hn),
   siPure_mono fun n hn => frag_validN_iff.mpr ((H n).mp hn)⟩

end view

section excl_auth
open BI ExclAuth
variable [Sbi SI PROP] [OFE SI A]

@[rocq_alias excl_auth_agreeI]
theorem excl_auth_agreeI (a b : A) :
    ✓[SI] ((●E a : ExclAuthR (SI := SI) (A := A)) • (◯E b)) ⊢@{PROP} a ≡[SI] b :=
  siPure_mono fun _ h => agreeN h

end excl_auth

section frac_agree
open BI DFracAgree
variable [Sbi SI PROP] {A : Type _} [OFE SI A]

@[rocq_alias frac_agree_validI]
theorem frac_agree_validI (q : Qp) (a : A) :
    ✓[SI] (Frac.mk (SI := SI) q a) ⊣⊢@{PROP} ⌜q.val ≤ 1⌝ :=
  (dfrac_agree_validI (DFrac.own q) a).trans
    ⟨pure_mono DFrac.valid_own.mp, pure_mono DFrac.valid_own.mpr⟩

@[rocq_alias frac_agree_validI_2]
theorem frac_agree_validI_2 (q1 q2 : Qp) (a b : A) :
    ✓[SI] (Frac.mk (SI := SI) q1 a • Frac.mk q2 b) ⊣⊢@{PROP}
      ⌜(q1 + q2).val ≤ 1⌝ ∧ a ≡[SI] b :=
  (dfrac_agree_validI_2 (DFrac.own q1) (DFrac.own q2) a b).trans
    (and_congr_left ⟨pure_mono DFrac.valid_own.mp, pure_mono DFrac.valid_own.mpr⟩)

end frac_agree

end Iris
