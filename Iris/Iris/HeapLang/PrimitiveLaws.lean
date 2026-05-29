module

public import Iris.HeapLang.Syntax
public import Iris.HeapLang.Semantics
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Adequacy
public import Iris.ProgramLogic.Lifting
public import Iris.BI.Lib.GenHeap
public import Iris.ProofMode
public import Std.Data.ExtTreeMap

@[expose] public section
namespace Iris.HeapLang

open Iris ProgramLogic Language.Notation Std

instance : OFE Val := OFE.ofDiscrete _ Eq_Equivalence
instance : InfiniteType Loc where
  enum n := .mk n
  enum_inj n m := by grind
instance : Inhabited State := ⟨.empty, .empty⟩

instance : Language.PureExec True 1 hl(if #true then {e1} else {e2}) e1 where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    constructor
    · intro σ
      exists e1, σ, []
      refine BaseStep.ContextStep.intro (K := []) ?_
      constructor
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues (Exp.if (.val (.lit (.bool true))) e1 e2) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        cases heq
        simp [toVal]
      have Hbase := EctxLanguage.baseStep_of_primStep Hstep hsr
      cases Hbase
      case ifTrueS => exact ⟨rfl, rfl, rfl, rfl⟩
      all_goals contradiction

instance {f x : Binder} {e : Exp} {v : Val} : Language.PureExec True 1 hl(v(rec f x := e) {v}) (Exp.subst x v (Exp.subst f (hl_val(rec f x := e)) e)) where
  pureExec _ := by
    refine Relation.Iterate.head ?_ (.rfl _)
    constructor
    · intro σ
      exists (Exp.subst x v (Exp.subst f (hl_val(rec f x := e)) e)), σ, []
      refine BaseStep.ContextStep.intro (K := []) ?_
      apply BaseStep.betaS
      simp [Exp.subst]
      sorry
    · intro σ1 σ2 κs e2' efs Hstep
      have hsr : EctxLanguage.SubredexesAreValues hl(v(rec f x := e) {↑v}) := by
        apply EctxItemLanguage.subredexes_are_values
        intro Ki e_inner heq
        cases Ki <;> try (cases heq; done)
        · cases heq; simp [toVal, expToVal]
        · cases heq; simp
      have Hbase := EctxLanguage.baseStep_of_primStep Hstep hsr
      cases Hbase

      case betaS => exact ⟨rfl, rfl, sorry, rfl⟩
      -- all_goals contradiction

section HeapLangGS

abbrev HeapF := fun V => Std.ExtTreeMap Loc V compare

class HeapLangGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGpreS GF where
  heap_pre : gen_HeapGPreS PNat Loc (Option Val) GF HeapF

attribute [reducible, instance] HeapLangGpreS.heap_pre

class HeapLangGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGS_gen hlc GF where
  heap : gen_HeapGS PNat Loc (Option Val) GF HeapF

attribute [reducible, instance] HeapLangGS.heap

instance HeapLangState [HeapLangGS hlc GF] : StateInterp State Observation GF where
  stateInterp σ _ _ _ := gen_heap_interp (F := PNat) (GF := GF) (H := HeapF) σ.heap

set_option allowUnsafeReducibility true
attribute [reducible, instance] StateInterp.stateInterp

instance HeapLang [HeapLangGS hlc GF] : IrisGS_gen hlc Exp GF where
  numLatersPerStep n := 0
  forkPost v := iprop(True)
  stateInterp_mono σ ns obs nt := by
    iintro H
    simp only [stateInterp]
    iframe H

end HeapLangGS

section NotationOverride

variable {GF : BundledGFunctors} {hlc : HasLC}
variable [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}

notation l " ↦{" dq "} " v => pointsTo l dq (Option.some v)
notation l " ↦ " v => pointsTo l (DFrac.own 1) (Option.some v)

end NotationOverride

section Adequacy

theorem heap_adequacy [HeapLangGpreS .hasLC GF] (e : Exp) σ (φ : Val → Prop) :
  (∀ [HeapLangGS .hasLC GF], ⊢@{IProp GF} (WP e {{ v, ⌜φ v⌝ }})) →
  adequate .NotStuck e σ (fun v _ => φ v) := by
  intro Hwp
  refine wp_adequacy (GF := GF) .NotStuck e σ φ ?_
  intro inst κs
  istart
  imod iOwn_alloc (E := HeapLangGpreS.heap_pre.heap.elem)
    (HeapView.Auth (.own One.one) (Std.PartialMap.map (fun  v => toAgree $ LeibnizO.mk v) σ.heap))
    HeapView.auth_one_valid with ⟨%γ, H⟩
  letI : HeapLangGS .hasLC GF := ⟨⟨γ⟩⟩
  imodintro
  iexists (fun σ _ => iOwn (E := HeapLangGpreS.heap_pre.heap.elem) γ
    (HeapView.Auth (.own One.one) (Std.PartialMap.map (fun v => toAgree $ LeibnizO.mk v) σ.heap)))
  iexists (fun _ => iprop(True))
  dsimp only
  iframe H
  exact Hwp

end Adequacy

section Lifting

variable {GF : BundledGFunctors} {hlc : HasLC}
variable [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}

theorem wp_if_true {e1 e2 : Exp} :
  ▷ WP e1 @ s; E {{ Φ }}
  ⊢ WP hl(if #true then {e1} else {e2}) @s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_pure_step_fupd (φ := True) (Hφ := True.intro) (n := 1) (e₂ := e1) (E₂ := E)
  · infer_instance
  · simp only [Nat.repeat]
    iintro !> !> !> -; iframe

theorem wp_rec {f x : Binder} (e : Exp) (v : Val) :
  ▷ WP ((e.subst f hl_val(rec f x := e)).subst x v) @ s; E {{ Φ }}
  ⊢@{IProp GF} WP hl(v(rec f x := e) {v}) @ s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_pure_step_fupd (φ := True) (Hφ := True.intro) (n := 1)
    (e₂ := (e.subst f hl_val(rec f x := e)).subst x v) (E₂ := E)
  · infer_instance
  · simp only [Nat.repeat]
    iintro !> !> !> -; iframe

theorem wp_alloc (v : Val) :
  ⊢ (WP (hl(ref(v(v)))) @ s; E {{ l, ∃ l' : Loc, ⌜l = .lit (.loc l')⌝ ∗ (l' ↦ v)}} : IProp GF) := by
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_sep
  simp only [stateInterp]
  let l := (List.fresh σ₁.heap.keys).choose
  have Hne : get? (M := HeapF) σ₁.heap l = .none := by
    simp only [get?, getElem?_eq_none_iff]
    rw [←Std.ExtTreeMap.mem_keys]
    exact (List.fresh σ₁.heap.keys).choose_spec
  isplitr
  · imodintro
    ipure_intro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exists [], (.val (.lit (.loc l))), (σ₁.initHeap l 1 v), []
    refine BaseStep.ContextStep.intro (K := []) ?_
    constructor
    · simp
    · intro i Hzero Hbound
      obtain ⟨⟩ : i = 0 := by grind
      rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
      exact Hne
  imod gen_heap_alloc _ (.some v) _ Hne $$ Hσ with ⟨Hσ, Hpt⟩
  imodintro
  iintro %e₂ %σ₂ %eₜ %Heq
  inext
  iintro Hcr
  have Hred : BaseStep.Reducible (hl(ref(v(v))), σ₁) := by
    exists [], (.val (.lit (.loc l))), (σ₁.initHeap l 1 v), []
    constructor
    · decide
    · intro i Hzero Hbound
      obtain ⟨⟩ : i = 0 := by grind
      rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
      exact Hne
  have Hbase := EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Heq
  cases Hbase
  case allocNS l' Hpos Hi =>
    simp only [Int.cast_ofNat_Int, List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
    have heq_heap : (σ₁.initHeap l' 1 v).heap = σ₁.heap.insert l' (some v) := by
      simp only [State.initHeap, Int.toNat_one]
      show List.foldl (fun h i => h.insert (l' + (i : Int)) (some v)) σ₁.heap (List.range 1) = _
      have : List.range 1 = [0] := by decide
      rw [this]
      simp only [List.foldl, Int.ofNat_zero]
      congr 1
      ext
      change l'.n + 0 = l'.n
      omega
    unfold HeapLang; dsimp only
    unfold HeapLangState; dsimp only
    rw [heq_heap]
    simp only [stateInterp]
    iframe Hσ
    iexists l'
    isplitr
    · ipure; rfl
    · iframe Hpt

end Lifting

end Iris.HeapLang
