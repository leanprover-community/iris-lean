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

/-- The state interpretation is closed under bumping the step counter. In
iris-lean this is trivial, since the heap_lang `stateInterp` ignores the step
index. Mirrors `state_interp_step` in `case_studies/heaplang/fixes.v`. -/
theorem state_interp_step [HeapLangGS hlc GF] (σ : State) (ns : Nat)
    (κs : List Observation) (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt ⊢ |==> stateInterp (GF := GF) σ (ns + 1) κs nt := by
  iintro H
  imodintro
  iexact H

end HeapLangGS

section Adequacy

theorem heap_adequacy [HeapLangGpreS .hasLC GF] (e : Exp) σ (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC GF], ⊢@{IProp GF} (WP e {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck e σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) .NotStuck e σ φ ?_
  intro inst κs
  imod iOwn_alloc (E := GhostMapG.elem)
    (HeapView.Auth (H := HeapF) (.own One.one)
    (Std.PartialMap.map (fun v => toAgree $ LeibnizO.mk v) σ.heap))
    HeapView.auth_one_valid with ⟨%γ, H⟩
  letI _ : HeapLangGS .hasLC GF := ⟨⟨γ⟩⟩
  imodintro
  iexists (fun σ _ => iOwn (E := GhostMapG.elem) γ
    (HeapView.Auth (H := HeapF) (.own One.one)
    (Std.PartialMap.map (fun v => toAgree $ LeibnizO.mk v) σ.heap)))
  iexists (fun _ => iprop(True))
  iframe H
  exact Hwp

end Adequacy

section Lifting

variable {GF : BundledGFunctors} {hlc : HasLC}
variable [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}

open EctxLanguage

theorem wp_snd {v1 v2 : Val} : ▷ Φ v2 ⊢ WP hl(snd(v(({v1}, {v2})))) @s; E {{ Φ }} := by
  iintro HΦ
  iapply wp_pure_step_fupd (Hφ := True.intro)
  dsimp only [Nat.repeat]
  iintro !> !> !> -; iframe
  iapply wp_value $$ HΦ
  constructor; rfl

theorem wp_if_true {e1 e2 : Exp} :
    ▷ WP e1 @ s; E {{ Φ }} ⊢ WP hl(if #true then {e1} else {e2}) @s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_pure_step_fupd (Hφ := True.intro)
  dsimp only [Nat.repeat]
  iintro !> !> !> -; iframe

theorem wp_if_false {e1 e2 : Exp} :
    ▷ WP e2 @ s; E {{ Φ }} ⊢ WP hl(if #false then {e1} else {e2}) @s; E {{ Φ }} := by
  iintro Hwp
  iapply wp_pure_step_fupd (Hφ := True.intro)
  dsimp only [Nat.repeat]
  iintro !> !> !> -; iframe

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

/-- Fancy-update-flavoured fork rule. Mirrors `wp_fork_fupd` in
`case_studies/heaplang/fixes.v`. -/
theorem wp_fork_fupd {e : Exp} :
    (▷ |={E}=> (WP e @ s; ⊤ {{ _v, True }} ∗ Φ (hl_val(#())))) ⊢
      WP hl(fork({e})) @ s; E {{ Φ }} := by
  iintro HeΦ
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
  imod HeΦ with ⟨Hwp, HΦ⟩
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
    List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil]
  specialize Hi 0 (by simp) (by simp)
  rw [show l' + (0 : Int) = l' by cases l'; simp only [HAdd.hAdd, Loc.mk.injEq]; grind] at Hi ⊢
  imod genHeap_alloc (v := some v) Hi $$ Hσ with ⟨Hσ, Hpt⟩
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

theorem wp_free {l : Loc} {v : Val} :
    ▷ (l ↦ some v)
    ⊢@{IProp GF} WP (Exp.free (.val (.lit (.loc l)))) @ s; E
      {{ v'', ⌜v'' = Val.lit BaseLit.unit⌝ ∗ (l ↦ (none : Option Val)) }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (Exp.free (.val (.lit (.loc l))), σ₁)⌝ $$ []
  · ipureintro
    exists [], (.val (.lit .unit)), (σ₁.initHeap l 1 none), []
    refine BaseStep.freeS l v _ ?_; grind
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i v'' H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil,
    Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := (none : Option Val)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ
  isplit <;> try itrivial
  iexists .lit .unit
  iframe Hpt
  ipureintro; simp [toVal]

theorem wp_xchg {l : Loc} {v w : Val} :
    ▷ (l ↦ some v)
    ⊢@{IProp GF} WP (Exp.xchg (.val (.lit (.loc l))) (.val w)) @ s; E
      {{ v'', ⌜v'' = v⌝ ∗ (l ↦ some w) }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (Exp.xchg (.val (.lit (.loc l))) (.val w), σ₁)⌝ $$ []
  · ipureintro
    exists [], (.val v), (σ₁.initHeap l 1 w), []
    refine BaseStep.xchgS l v w _ ?_; grind
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i v1' H
  obtain rfl : v = v1' := by
    rw [Hpt] at H
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
    exact H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil,
    Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := (some w : Option Val)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ
  isplit <;> try itrivial
  iexists v
  iframe Hpt
  ipureintro; simp [toVal]

theorem wp_faa {l : Loc} {i1 i2 : Int} :
    ▷ (l ↦ some (Val.lit (.int i1)))
    ⊢@{IProp GF} WP (Exp.faa (.val (.lit (.loc l))) (.val (.lit (.int i2)))) @ s; E
      {{ v'', ⌜v'' = Val.lit (.int i1)⌝ ∗ (l ↦ some (Val.lit (.int (i1 + i2)))) }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %Hpt : ⌜σ₁.get? l = .some (.some (Val.lit (.int i1)))⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred :
      ⌜BaseStep.Reducible (Exp.faa (.val (.lit (.loc l))) (.val (.lit (.int i2))), σ₁)⌝ $$ []
  · ipureintro
    exists [], (.val (.lit (.int i1))), (σ₁.initHeap l 1 (some (.lit (.int (i1 + i2))))), []
    refine BaseStep.faaS l i1 i2 _ ?_; grind
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i i1' H
  obtain rfl : i1 = i1' := by
    rw [Hpt] at H
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
      Val.lit.injEq, BaseLit.int.injEq] at H
    exact H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int, List.foldl_nil,
    Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := (some (Val.lit (.int (i1 + i2))) : Option Val)) $$ [$Hσ $Hpt]
    with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ
  isplit <;> try itrivial
  iexists Val.lit (.int i1)
  iframe Hpt
  ipureintro; simp [toVal]

end Lifting

end Iris.HeapLang
