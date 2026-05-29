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

instance HeapLang [HeapLangGS hlc GF] : IrisGS_gen hlc Exp GF where
  numLatersPerStep n := 0
  forkPost v := iprop(True)
  stateInterp_mono σ ns obs nt := by
    iintro H
    simp only [stateInterp]
    iframe H

end HeapLangGS

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

theorem wp_if_false {e1 e2 : Exp} :
  ▷ WP e2 @ s; E {{ Φ }}
  ⊢ WP hl(if #false then {e1} else {e2}) @s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_pure_step_fupd (φ := True) (Hφ := True.intro) (n := 1) (e₂ := e2) (E₂ := E)
  · infer_instance
  · simp only [Nat.repeat]
    iintro !> !> !> -; iframe

theorem wp_rec {f x : Binder} {e : Exp} {v : Val} :
  ▷ WP ((e.subst f (.rec_ f x e)).subst x v) @ s; E {{ Φ }}
  ⊢@{IProp GF} WP (Exp.app (.val (.rec_ f x e)) v) @ s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_pure_step_fupd (φ := True) (Hφ := True.intro) (n := 1)
    (e₂ := (e.subst f (.rec_ f x e)).subst x v) (E₂ := E)
  · infer_instance
  · simp only [Nat.repeat]
    iintro !> !> !> -; iframe

theorem wp_fork {e : Exp} :
  ▷ Φ (.lit .unit) ∗ ▷ WP e @ s; ⊤ {{ _v, True }} ⊢ WP hl(fork({e})) @ s; E {{ Φ }} := by
  iintro ⟨HΦ, Hwp⟩
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  have Hred : BaseStep.Reducible (hl(fork({e})), σ₁) := by
    exists [], (.val (.lit .unit)), σ₁, [e]
    simp [BaseStep.baseStep]
    constructor
  isplitr
  · ipure_intro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact (EctxLanguage.primStep_reducible_of_baseStep_reducible Hred)
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Heq)
  unfold HeapLang HeapLangState; dsimp only
  iframe Hσ
  imodintro
  isplitr [Hwp]
  · iexists (.lit .unit)
    isplit
    · ipure_intro; rfl
    · iframe HΦ
  · iapply BI.BigSepL.bigSepL_singleton
    iframe Hwp

theorem wp_alloc (v : Val) :
  ⊢ (WP (hl(ref({v}))) @ s; E {{ l, ∃ l' : Loc, ⌜l = .lit (.loc l')⌝ ∗ (l' ↦ (Option.some v))}} : IProp GF) := by
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  let l := (List.fresh σ₁.heap.keys).choose
  have Hne : σ₁.get? l = .none := by
    simp [State.get?, get?, getElem?_eq_none_iff, ←Std.ExtTreeMap.mem_keys]
    exact (List.fresh σ₁.heap.keys).choose_spec
  have Hred : BaseStep.Reducible (hl(ref({v})), σ₁) := by
    exists [], (.val (.lit (.loc l))), (σ₁.initHeap l 1 v), []
    constructor
    · simp
    · intro i Hzero Hbound
      rw [show l + (i : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
      exact Hne
  isplitr
  · ipure_intro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact (EctxLanguage.primStep_reducible_of_baseStep_reducible Hred)
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Heq)
  rename_i l' Hpo Hi
  simp only [Int.cast_ofNat_Int, Algebra.BigOpL.bigOpL_nil,
    Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  specialize Hi 0 (by simp) (by simp)
  rw [show l' + (0 : Int) = l' by cases l'; simp only [HAdd.hAdd, Loc.mk.injEq]; grind] at Hi ⊢
  imod gen_heap_alloc _ (.some v) _ Hi $$ Hσ with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ
  isplit
  · iexists (.lit (.loc l'))
    isplit
    · ipure_intro; rfl
    · iexists l'
      iframe Hpt
      ipure_intro; rfl
  · ipure_intro; simp

theorem wp_load {l : Loc} {q} {v : Val} :
  ▷ (l ↦{q} (Option.some v))
  ⊢ (WP hl(!{.val (.lit (.loc l))}) @ s; E {{ v', ⌜v = v'⌝ ∗ (l ↦{q} (Option.some v')) }} : IProp GF) := by
  iintro >Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %Hpt : ⌜σ₁.get? l = v⌝ $$ [Hσ Hpt]
  · iapply bupd_elim
    simp only [State.get?]
    iapply gen_heap_valid $$ [$Hσ $Hpt]
  ihave %Hred : ⌜BaseStep.Reducible (hl(!{.val (.lit (.loc l))}), σ₁)⌝ $$ []
  · ipure_intro
    exists [], (.val v), σ₁, []
    constructor
    rw [Hpt]; simp
  isplitr
  · ipure_intro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact (EctxLanguage.primStep_reducible_of_baseStep_reducible Hred)
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Heq)
  rename_i v'' H
  rw [Hpt] at H; simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq] at H
  subst H
  simp only [Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  imodintro
  isplit
  · iexists v; iframe Hpt
    ipure_intro
    simp [toVal]
  · itrivial

theorem wp_store {l : Loc} {v v' : Val} {e : Exp} :
  toVal e = Option.some v →
  ▷ (l ↦ (Option.some v'))
  ⊢ (WP hl({.val (.lit (.loc l))} ← {v}) @ s; E {{ v'', ⌜v'' = Val.lit .unit⌝ ∗ (l ↦ (Option.some v)) }} : IProp GF) := by
  iintro %Heq >Hpt
  iapply wp_lift_atomic_step
  · simp [toVal]
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases gen_heap_valid $$ [$Hσ $Hpt] with >%Heq'
    ipure_intro; assumption
  ihave %Hred : ⌜BaseStep.Reducible (hl({.val (.lit (.loc l))} ← {v}), σ₁)⌝ $$ []
  · ipure_intro
    exists [], (.val (.lit .unit)), (σ₁.initHeap l 1 v), []
    refine BaseStep.storeS _ v' _ _ ?_
    rw [Hpt]; simp
  isplitr
  · ipure_intro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact (EctxLanguage.primStep_reducible_of_baseStep_reducible Hred)
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred Heq)
  rename_i v'' H
  rw [Hpt] at H; simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq] at H
  subst H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil,
    Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]

  imod gen_heap_update (v₂ := .some v) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ
  isplit
  · iexists (.lit .unit)
    iframe Hpt
    ipure_intro
    simp [toVal]
  · itrivial

end Lifting

end Iris.HeapLang
