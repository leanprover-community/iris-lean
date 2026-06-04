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
  heap_pre : genHeapPreS PNat Loc (Option Val) GF HeapF

attribute [reducible, instance] HeapLangGpreS.heap_pre

class HeapLangGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGS_gen hlc GF where
  heap : genHeapGS PNat Loc (Option Val) GF HeapF

attribute [reducible, instance] HeapLangGS.heap

instance HeapLangState [HeapLangGS hlc GF] : StateInterp State Observation GF where
  stateInterp σ _ _ _ := genHeapInterp (F := PNat) (GF := GF) (H := HeapF) σ.heap

instance HeapLang [HeapLangGS hlc GF] : IrisGS_gen hlc Exp GF where
  numLatersPerStep n := 0
  forkPost v := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

end HeapLangGS

section Adequacy

theorem heap_adequacy [HeapLangGpreS .hasLC GF] (e : Exp) σ (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC GF], ⊢@{IProp GF} (WP e {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck e σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) .NotStuck e σ φ ?_
  intro inst κs
  imod iOwn_alloc (E := GhostMapG.elem (K := Loc) (V := Option Val) (F := PNat) (H := HeapF))
    (HeapView.Auth (H := HeapF) (.own One.one)
      (Std.PartialMap.map (fun v : Option Val => toAgree (LeibnizO.mk v)) σ.heap))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem (K := Loc) (V := GName) (F := PNat) (H := HeapF))
    (HeapView.Auth (H := HeapF) (.own One.one)
      (Std.PartialMap.map (fun g : GName => toAgree (LeibnizO.mk g))
        (∅ : HeapF GName)))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  letI _ : HeapLangGS .hasLC GF := ⟨⟨γh, γm⟩⟩
  imodintro
  iexists (fun σ _ => Iris.genHeapInterp (F := PNat) (GF := GF) (H := HeapF) σ.heap)
  iexists (fun _ => iprop(True))
  isplitl [Hh Hm]
  · simp only [Iris.genHeapInterp]
    iexists (∅ : HeapF GName)
    isplitr
    · ipureintro
      intro k hk
      simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk
    unfold ghost_map_auth
    simp only [Std.PartialMap.map, Std.PartialMap.bindAlter]
    iframe Hh Hm
  · exact Hwp

end Adequacy

section Lifting

variable {GF : BundledGFunctors} {hlc : HasLC}
variable [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}

open EctxLanguage

-- TODO use hl syntax everywhere possible

theorem wp_rec {f x : Binder} {e : Exp} {v : Val} :
    ▷ WP ((e.subst f (.rec_ f x e)).subst x v) @ s; E {{ Φ }}
    ⊢  WP (Exp.app (.val (.rec_ f x e)) v) @ s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_pure_step_fupd (Hφ := True.intro)
  dsimp only [Nat.repeat]
  iintro !> !> !> -; iframe

theorem wp_fork {e : Exp} :
    ▷ Φ (hl_val(#())) ∗ ▷ WP e @ s; ⊤ {{ _v, True }} ⊢ WP hl(fork({e})) @ s; E {{ Φ }} := by
  iintro ⟨HΦ, Hwp⟩
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  have Hred : BaseStep.Reducible (hl(fork({e})), σ₁) :=
    ⟨[], hl(#BaseLit.unit), σ₁, [e], by constructor⟩
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact (primStep_reducible_of_baseStep_reducible Hred)
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  iframe Hσ
  imodintro
  isplitr [Hwp]
  · iexists _
    iframe HΦ
    ipureintro; rfl
  · iapply BI.BigSepL.bigSepL_singleton
    iframe Hwp

theorem wp_alloc (v : Val) :
    ⊢ WP (hl(ref({v}))) @ s; E {{ l, ∃ l' : Loc, ⌜l = .lit (.loc l')⌝ ∗ (l' ↦ (some v))}} := by
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  let l := (List.fresh σ₁.heap.keys).choose
  have Hne : σ₁.get? l = .none := by
    simpa [State.get?, get?, getElem?_eq_none_iff, ←Std.ExtTreeMap.mem_keys]
      using (List.fresh σ₁.heap.keys).choose_spec
  have Hred : BaseStep.Reducible (hl(ref({v})), σ₁) := by
    exists [], (.val (.lit (.loc l))), (σ₁.initHeap l 1 v), []
    constructor
    · trivial
    · intro i Hzero Hbound
      rw [show l + (i : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
      exact Hne
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  rcases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i l' Hpo Hi
  simp only [Int.cast_ofNat_Int, Algebra.BigOpL.bigOpL_nil, Int.toNat_one, List.range_one,
    List.foldl_cons, List.foldl_nil]
  specialize Hi 0 (by simp) (by simp)
  rw [show l' + (0 : Int) = l' by cases l'; simp only [HAdd.hAdd, Loc.mk.injEq]; grind] at Hi ⊢
  imod genHeap_alloc (v := some v) Hi $$ Hσ with ⟨Hσ, Hpt, _Hmt⟩
  imodintro
  -- FIXME: can iframe should solve emp?
  iframe Hσ
  isplit <;> try itrivial
  iexists hl_val(#(BaseLit.loc l'))
  isplit; ipureintro; rfl
  iexists _
  iframe Hpt
  itrivial

theorem wp_load {l : Loc} {q} {v : Val} :
    ▷ (l ↦{q} (some v))
    ⊢@{IProp GF} WP hl(!v({(.lit (.loc l))})) @ s; E {{ v', ⌜v = v'⌝ ∗ (l ↦{q} (some v')) }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  ihave %Hpt : ⌜σ₁.get? l = v⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(!{.val (.lit (.loc l))}), σ₁)⌝ $$ []
  · ipureintro
    exists [], (.val v), σ₁, []
    constructor; simp [Hpt]
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i v'' H
  rw [Hpt] at H; simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq] at H
  subst H
  simp only [Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  imodintro
  isplit <;> try itrivial
  iexists _; iframe Hpt
  ipureintro; simp [toVal]

theorem wp_store {l : Loc} {v v' : Val} :
    ▷ (l ↦ (some v'))
    ⊢@{IProp GF} WP hl(v({(.lit (.loc l))}) ← {v}) @ s; E
      {{ v'', ⌜v'' = hl_val(#())⌝ ∗ (l ↦ some v) }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl({.val (.lit (.loc l))} ← {v}), σ₁)⌝ $$ []
  · ipureintro
    exists [], (.val (.lit .unit)), (σ₁.initHeap l 1 v), []
    refine BaseStep.storeS _ v' _ _ ?_; grind
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i v'' H
  rw [Hpt] at H; simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq] at H
  subst H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil,
    Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := .some v) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ
  isplit <;> try itrivial
  iexists .lit .unit
  iframe Hpt
  ipureintro; simp [toVal]

theorem wp_cmpXchg_fail {l : Loc} {q} {v' : Val} {e1 : Exp} {v1 : Val} {e2 : Exp} {v2 : Val}
    (Heq1 : toVal e1 = .some v1) (Heq2 : toVal e2 = .some v2) (Heq3 : v'.compareSafe v1)
    (Heq4 : decide (v' = v1) = false) :
      ▷ (l ↦{q} some v')
      ⊢ (WP hl(cmpXchg(v({.lit (BaseLit.loc l)}), {e1}, {e2})) @ s; E
          {{ v'', ⌜v'' = hl_val(({v'}, #(BaseLit.bool false)))⌝ ∗ l ↦{q} some v' }}) := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(cmpXchg(v({.lit (BaseLit.loc l)}), {e1}, {e2})), σ₁)⌝ $$ []
  · ipureintro
    exists [], hl(v(({v'}, #(BaseLit.bool false)))), σ₁, []
    rw [show e1 = ToVal.ofVal v1 by grind, show e2 = ToVal.ofVal v2 by grind]
    constructor <;> grind
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i Heq4 H
  rw [Hpt] at H
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
  subst H
  simp only [Algebra.BigOpL.bigOpL_nil]
  subst Heq4; simp only [toVal, Option.some.injEq] at Heq1 Heq2
  subst Heq1; subst Heq2
  simp only [Heq4, Bool.false_eq_true, ↓reduceIte]
  imodintro
  iframe Hσ
  isplit <;> try itrivial
  iexists hl_val(({v'}, #(BaseLit.bool false)))
  iframe Hpt
  ipureintro; simp [toVal]

theorem wp_cmpXchg_true {l : Loc} {v' : Val} {e1 : Exp} {v1 : Val} {e2 : Exp} {v2 : Val}
    (Heq1 : toVal e1 = .some v1) (Heq2 : toVal e2 = .some v2) (Heq3 : v'.compareSafe v1)
    (Heq4 : decide (v' = v1) = true) :
      ▷ (l ↦ some v')
      ⊢ WP hl(cmpXchg(v({.lit (BaseLit.loc l)}), {e1}, {e2})) @ s; E
        {{ v'', ⌜v'' = hl_val(({v'}, #(BaseLit.bool true)))⌝ ∗ l ↦ some v2 }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(cmpXchg(v({.lit (BaseLit.loc l)}), {e1}, {e2})), σ₁)⌝ $$ []
  · ipureintro
    exists [], hl(v(({v'}, #(BaseLit.bool true)))), (σ₁.initHeap l 1 (some v2)), []
    rw [show e1 = ToVal.ofVal v1 by grind, show e2 = ToVal.ofVal v2 by grind]
    constructor <;> grind
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i v1' v2' vl' _ _ Heq4 H
  rw [Hpt] at H
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
  subst H
  simp only [Algebra.BigOpL.bigOpL_nil]
  subst Heq4; simp only [toVal, Option.some.injEq] at Heq1 Heq2
  subst Heq1; subst Heq2
  simp only [Heq4, ↓reduceIte, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := .some v2') $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ
  isplit <;> try itrivial
  iexists hl_val(({v'}, #(BaseLit.bool true)))
  iframe Hpt
  ipureintro; simp [toVal]

end Lifting

end Iris.HeapLang
