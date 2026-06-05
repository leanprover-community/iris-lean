module

public import Iris.HeapLang.Syntax
public import Iris.HeapLang.Semantics
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Adequacy
public import Iris.ProgramLogic.Lifting
public import Iris.BI.Lib.GenHeap
public import Iris.BI.Lib.ProphMap
public import Iris.Std.GenSetsInstances
public import Iris.ProofMode
public import Std.Data.ExtTreeMap

@[expose] public section
namespace Iris.HeapLang

open Iris ProgramLogic Language.Notation Std

section HeapLangGS

abbrev HeapF := fun V => Std.ExtTreeMap Loc V compare

/-- The finite-map type used by the heap_lang prophecy ghost state: a map from
`ProphId` to the prophecy's outstanding resolution list. Mirrors the Rocq
`gmap proph_id (list val)` used in `proph_map`. -/
abbrev ProphMapF := fun V => Std.ExtTreeMap ProphId V compare

class HeapLangGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGpreS GF where
  heap_pre : genHeapPreS PNat Loc (Option Val) GF HeapF
  proph_pre : prophMapPreS PNat ProphId (Val × Val) GF ProphMapF

attribute [reducible, instance] HeapLangGpreS.heap_pre
attribute [reducible, instance] HeapLangGpreS.proph_pre

class HeapLangGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGS_gen hlc GF where
  heap : genHeapGS PNat Loc (Option Val) GF HeapF
  proph : prophMapGS (F := PNat) ProphId (Val × Val) GF ProphMapF

attribute [reducible, instance] HeapLangGS.heap
attribute [reducible, instance] HeapLangGS.proph

instance HeapLangState [HeapLangGS hlc GF] : StateInterp State Observation GF where
  stateInterp σ _ κs _ := iprop(
    genHeapInterp (F := PNat) (GF := GF) (H := HeapF) σ.heap ∗
    prophMapInterp (F := PNat) (GF := GF) (H := ProphMapF) κs σ.usedProphId)

/-- The state interpretation as a separating conjunction of the heap interp and
the prophecy-map interp. Used to destruct `Hσ` into its two conjuncts after
`wp_lift_atomic_step`. -/
theorem stateInterp_split [HeapLangGS hlc GF] (σ : State) (ns : Nat)
    (κs : List Observation) (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt ⊣⊢
      iprop(genHeapInterp (F := PNat) (GF := GF) (H := HeapF) σ.heap ∗
            prophMapInterp (F := PNat) (GF := GF) (H := ProphMapF) κs σ.usedProphId) :=
  Iris.BI.BIBase.BiEntails.rfl

/-- Normalize a `[] ++ κs` argument to `κs`. Used to rephrase `prophMapInterp`
hypotheses introduced before a step whose observations are `[]` get substituted
in by `cases`. The two sides are definitionally equal. -/
theorem prophMapInterp_nil_append [HeapLangGS hlc GF] (κs : List Observation)
    (ps : Std.ExtTreeSet ProphId) :
    iprop(prophMapInterp (F := PNat) (GF := GF) (H := ProphMapF) ([] ++ κs) ps) ⊣⊢
    iprop(prophMapInterp (F := PNat) (GF := GF) (H := ProphMapF) κs ps) :=
  Iris.BI.BIBase.BiEntails.rfl

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
  imod iOwn_alloc (E := GhostMapG.elem (K := Loc) (V := Option Val) (F := PNat) (H := HeapF))
    (HeapView.Auth (H := HeapF) (.own One.one)
      (Std.PartialMap.map (fun v : Option Val => toAgree (LeibnizO.mk v)) σ.heap))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem (K := Loc) (V := GName) (F := PNat) (H := HeapF))
    (HeapView.Auth (H := HeapF) (.own One.one)
      (Std.PartialMap.map (fun g : GName => toAgree (LeibnizO.mk g))
        (∅ : HeapF GName)))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  imod (ProphMap.init (F := PNat) (V := Val × Val) (H := ProphMapF) κs σ.usedProphId)
    with ⟨%Gproph, Hproph⟩
  letI _ : HeapLangGS .hasLC GF := ⟨⟨γh, γm⟩, Gproph⟩
  imodintro
  iexists (fun σ κs => iprop(
    Iris.genHeapInterp (F := PNat) (GF := GF) (H := HeapF) σ.heap ∗
    Iris.prophMapInterp (F := PNat) (GF := GF) (H := ProphMapF) κs σ.usedProphId))
  iexists (fun _ => iprop(True))
  isplitl [Hh Hm Hproph]
  · isplitl [Hh Hm]
    · simp only [Iris.genHeapInterp]
      iexists (∅ : HeapF GName)
      isplitr
      · ipureintro
        intro k hk
        simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk
      unfold ghost_map_auth
      iframe Hh Hm
    · iexact Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  have Hred : BaseStep.Reducible (hl(fork({e})), σ₁) :=
    ⟨[], hl(#BaseLit.unit), σ₁, [e], by constructor⟩
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact (primStep_reducible_of_baseStep_reducible Hred)
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  imodintro
  isplitl [Hσ Hproph]
  · iapply (stateInterp_split σ₁ (ns + 1) obs' (nt + [e].length)).mpr
    iframe Hσ Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  have Hred : BaseStep.Reducible (hl(fork({e})), σ₁) :=
    ⟨[], hl(#BaseLit.unit), σ₁, [e], by constructor⟩
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact (primStep_reducible_of_baseStep_reducible Hred)
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  imod HeΦ with ⟨Hwp, HΦ⟩
  imodintro
  isplitl [Hσ Hproph]
  · iapply (stateInterp_split σ₁ (ns + 1) obs' (nt + [e].length)).mpr
    iframe Hσ Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
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
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Int.cast_ofNat_Int, Algebra.BigOpL.bigOpL_nil, Int.toNat_one,
    List.range_one, List.foldl_cons, List.foldl_nil]
  specialize Hi 0 (by simp) (by simp)
  rw [show l' + (0 : Int) = l' by cases l'; simp only [HAdd.hAdd, Loc.mk.injEq]; grind] at Hi ⊢
  imod genHeap_alloc (v := some v) Hi $$ Hσ with ⟨Hσ, Hpt, _Hmt⟩
  imodintro
  iframe Hσ Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
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
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Algebra.BigOpL.bigOpL_nil]
  iframe Hσ Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
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
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil, Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := .some v) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
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
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Algebra.BigOpL.bigOpL_nil]
  subst Heq4; simp only [toVal, Option.some.injEq] at Heq1 Heq2
  subst Heq1; subst Heq2
  simp only [Heq4, Bool.false_eq_true, ↓reduceIte]
  imodintro
  iframe Hσ Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
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
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Algebra.BigOpL.bigOpL_nil]
  subst Heq4; simp only [toVal, Option.some.injEq] at Heq1 Heq2
  subst Heq1; subst Heq2
  simp only [Heq4, ↓reduceIte, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := .some v2') $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
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
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil, Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := (none : Option Val)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
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
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil, Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := (some w : Option Val)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ Hproph
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
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
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
    simp only [Option.some.injEq, Val.lit.injEq, BaseLit.int.injEq] at H
    exact H
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil, Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := (some (Val.lit (.int (i1 + i2))) : Option Val)) $$ [$Hσ $Hpt]
    with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ Hproph
  isplit <;> try itrivial
  iexists Val.lit (.int i1)
  iframe Hpt
  ipureintro; simp [toVal]

/-- The state update of a `newProphS` step (insertion into `usedProphId`) is the
same set as `{p} ∪ usedProphId`, which is what `ProphMap.new_proph` returns. -/
theorem usedProph_insert_eq {ps : Std.ExtTreeSet ProphId compare} {p : ProphId} :
    ps.insert p = ({p} ∪ ps : Std.ExtTreeSet ProphId compare) := by
  apply Std.ExtTreeSet.ext_mem
  intro x
  rw [Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.mem_union_iff,
    Iris.Std.LawfulSet.mem_singleton, Std.LawfulEqCmp.compare_eq_iff_eq]
  constructor
  · rintro (rfl | h)
    · left; rfl
    · right; exact h
  · rintro (rfl | h)
    · left; rfl
    · right; exact h

/-- Allocate a fresh prophecy variable. Mirrors `wp_new_proph` in `iris.heap_lang.lifting`. -/
theorem wp_new_proph :
    ⊢ WP (Exp.newProph : Exp) @ s; E
        {{ v, ∃ p : ProphId, ∃ pvs : List (Val × Val),
              ⌜v = .lit (.prophecy p)⌝ ∗ proph p pvs }} := by
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  -- Pick a prophecy id fresh in the current `usedProphId`.
  obtain ⟨pf, Hpf⟩ := Iris.Std.List.fresh σ₁.usedProphId.toList
  have Hpf_contains : ¬ σ₁.usedProphId.contains pf := by
    intro hc; exact Hpf (Std.ExtTreeSet.mem_toList.mpr hc)
  have Hred : BaseStep.Reducible (Exp.newProph, σ₁) :=
    ⟨[], _, _, [], BaseStep.newProphS σ₁ pf Hpf_contains⟩
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i p' Hp'
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  -- Convert `¬ contains` to `∉` for `ProphMap.new_proph`.
  have Hp'_mem : p' ∉ σ₁.usedProphId :=
    fun hmem => Hp' (Std.ExtTreeSet.mem_iff_contains.symm.mp hmem)
  imod (ProphMap.new_proph p' σ₁.usedProphId obs' Hp'_mem) $$ Hproph
    with ⟨Hproph', Htok⟩
  imodintro
  simp only [stateInterp]
  iframe Hσ
  isplitl [Hproph']
  · -- Bridge `{p'} ∪ σ₁.usedProphId` (from new_proph) and `σ₁.usedProphId.insert p'`
    -- (from the newProphS constructor's output).
    rw [show ({p'} ∪ σ₁.usedProphId : Std.ExtTreeSet ProphId compare)
         = σ₁.usedProphId.insert p' from usedProph_insert_eq.symm]
    iexact Hproph'
  isplitl [Htok]
  · iexists hl_val(#(BaseLit.prophecy p'))
    isplit
    · ipureintro; simp [toVal]
    iexists p', _
    iframe Htok
    ipureintro; rfl
  · simp only [Algebra.BigOpL.bigOpL_nil]; itrivial

/-- The step-branch of `wp.pre`, exposed as the converse of `wp_lift_step_fupd`.
Given `e` non-value, a WP for `e` unfolds to the universal step-continuation. -/
theorem wp_open {Φ : Val → IProp GF} {e : Exp} :
    WP e @ s; E {{ Φ }} ⊢ wp.pre s (Wp.wp (PROP := IProp GF) s) E e Φ :=
  wp_unfold.mp

/-- `Resolve e (Val (LitProphecy p)) (Val w)` lifts a WP for the inner expression
`e` through the `Resolve` wrapper, consuming the front observation `(v_e, w)`
from the prophecy `p`. The inner WP is allowed to use the prophecy token
`proph p pvs` while reducing `e`; on completion the postcondition is closed
under reattaching the front observation. Mirrors `wp_resolve_strong` in Rocq
heap_lang's `primitive_laws.v`. -/
theorem wp_resolve_strong {e : Exp} {p : ProphId} {w : Val} {pvs : List (Val × Val)}
    (hatom : Language.Atomic (State := State) (Obs := Observation)
      Language.Atomicity.StronglyAtomic e)
    (hne : toVal e = none) :
    proph p pvs -∗
    (proph p pvs -∗ WP e @ s; E {{ v_e, ∃ pvs', proph p pvs' ∗
      ∀ pvs'', ⌜pvs' = (v_e, w) :: pvs''⌝ -∗ proph p pvs'' -∗ Φ v_e }}) -∗
    WP (Exp.resolve e (.val (.lit (.prophecy p))) (.val w)) @ s; E {{ Φ }} := by
  -- Mirrors Rocq `iris/heap_lang/primitive_laws.v:726–758`. The proof breaks
  -- the WP abstraction by unfolding `wp_unfold` directly on the inner WP for
  -- `e`, reverse-inducting on the outer observation list, and threading the
  -- trailing observation through the prophecy map via `ProphMap.resolve_proph`.
  iintro Hp HWPe
  iapply wp_lift_step_fupdN rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hheap, Hpmap⟩
  -- Extract `p ∈ σ₁.usedProphId` (pure conclusion via `ProphMap.agree`,
  -- preserving `Hpmap` and `Hp` via the `$` frame markers).
  icases ProphMap.agree (obs ++ obs') σ₁.usedProphId p pvs $$ [$Hpmap $Hp]
    with %Hagree
  have Hp_mem : p ∈ σ₁.usedProphId := Hagree.1
  have hp_contains : σ₁.usedProphId.contains p :=
    Std.ExtTreeSet.mem_iff_contains.mp Hp_mem
  -- Feed the prophecy token to the inner WP wand.
  ihave HWPe : iprop(WP e @ s; E {{ v_e, ∃ pvs', proph p pvs' ∗
      ∀ pvs'', ⌜pvs' = (v_e, w) :: pvs''⌝ -∗ proph p pvs'' -∗ Φ v_e }})
      $$ [Hp HWPe]
  · iapply HWPe; iexact Hp
  -- Convert HWPe via `wp_open` into `wp.pre`; then reduce via `hne` using
  -- the Lean-eq → iris-hyp bridge (`rw` on a Lean Prop goal).
  ihave HWPe := wp_open $$ HWPe
  -- Now HWPe : wp.pre s _ E e Φ_strong; reduce via match on `toVal e = none`.
  -- Reduce `wp.pre` using `hne` via a Lean-level rewrite on the `ihave` subgoal.
  -- We use `_` heavily and let Lean infer the unfolded shape.
  ihave HWPe := (show wp.pre s (Wp.wp (PROP := IProp GF) s) E e
      (fun v_e => iprop(∃ pvs', proph p pvs' ∗
        ∀ pvs'', ⌜pvs' = (v_e, w) :: pvs''⌝ -∗ proph p pvs'' -∗ Φ v_e)) ⊢ _
    by simp only [wp.pre, hne]; exact Iris.BI.BIBase.Entails.rfl) $$ HWPe
  -- Reverse-induct on the outer observation list `obs`.
  rcases hrev : obs.reverse with _ | ⟨lastObs, init_rev⟩
  · -- obs = []. Apply inner WP with inner obs = [], inner obs' = obs'.
    have hobs : obs = [] := List.reverse_eq_nil_iff.mp hrev
    subst hobs
    ihave Hσ_e : iprop(stateInterp σ₁ ns ([] ++ obs') nt) $$ [Hheap Hpmap]
    · iapply (stateInterp_split σ₁ ns ([] ++ obs') nt).mpr
      iframe Hheap
      iexact Hpmap
    imod HWPe $$ %_ %_ %_ %_ %_ Hσ_e with ⟨%Hred_e, HWPe⟩
    imodintro
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible]
      -- For NotStuck: extract the inner step from `Hred_e : PrimStep.Reducible`,
      -- convert to BaseStep via atomicity, then lift through Resolve.
      obtain ⟨κ_h, e'_h, σ'_h, efs_h, hprim_h⟩ := Hred_e
      have hval_h : (toVal e'_h).isSome := hatom.atomic hprim_h
      obtain ⟨v_h, rfl⟩ : ∃ v_h, e'_h = Exp.val v_h := by
        match e'_h, hval_h with | .val v_h, _ => exact ⟨v_h, rfl⟩
      have hbase_h : BaseStep e σ₁ κ_h (.val v_h) σ'_h efs_h :=
        primStep_val_baseStep hprim_h
      exact EctxLanguage.primStep_reducible_of_baseStep_reducible
        (resolve_reducible hatom ⟨κ_h, _, σ'_h, efs_h, hbase_h⟩ hp_contains)
    iintro %e₂ %σ₂ %eₜ %Hstep _Hcred
    exfalso
    obtain ⟨κ_inner, v_inner, hκ_eq, _, _, _⟩ :=
      step_resolve_decompose hatom Hstep
    exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp hκ_eq.symm).2
  · -- obs = init_rev.reverse ++ [lastObs]. Apply inner WP with
    -- inner obs = init_rev.reverse, inner obs' = lastObs :: obs'.
    have hobs : obs = init_rev.reverse ++ [lastObs] := by
      have hh := congrArg List.reverse hrev; simp at hh; exact hh
    subst hobs
    have hassoc : (init_rev.reverse ++ [lastObs]) ++ obs' =
        init_rev.reverse ++ (lastObs :: obs') := by simp
    ihave Hσ_e : iprop(stateInterp σ₁ ns (init_rev.reverse ++ (lastObs :: obs')) nt)
        $$ [Hheap Hpmap]
    · iapply (stateInterp_split σ₁ ns (init_rev.reverse ++ (lastObs :: obs')) nt).mpr
      iframe Hheap
      rw [← hassoc]; iexact Hpmap
    imod HWPe $$ %_ %_ %_ %_ %_ Hσ_e with ⟨%Hred_e, HWPe⟩
    imodintro
    isplitr
    · ipureintro
      cases s <;> simp only [Stuckness.MaybeReducible]
      -- For NotStuck: extract the inner step from `Hred_e : PrimStep.Reducible`,
      -- convert to BaseStep via atomicity, then lift through Resolve.
      obtain ⟨κ_h, e'_h, σ'_h, efs_h, hprim_h⟩ := Hred_e
      have hval_h : (toVal e'_h).isSome := hatom.atomic hprim_h
      obtain ⟨v_h, rfl⟩ : ∃ v_h, e'_h = Exp.val v_h := by
        match e'_h, hval_h with | .val v_h, _ => exact ⟨v_h, rfl⟩
      have hbase_h : BaseStep e σ₁ κ_h (.val v_h) σ'_h efs_h :=
        primStep_val_baseStep hprim_h
      exact EctxLanguage.primStep_reducible_of_baseStep_reducible
        (resolve_reducible hatom ⟨κ_h, _, σ'_h, efs_h, hbase_h⟩ hp_contains)
    iintro %e₂ %σ₂ %eₜ %Hstep Hcred
    obtain ⟨κ_inner, v_inner, hκ_eq, he₂_eq, Hbase_e, _⟩ :=
      step_resolve_decompose hatom Hstep
    -- κ_inner ++ [(p, (v_inner, w))] = init_rev.reverse ++ [lastObs]
    -- Cancel: κ_inner = init_rev.reverse, lastObs = (p, (v_inner, w))
    obtain ⟨hκ_inner_eq, hlast_eq⟩ :
        κ_inner = init_rev.reverse ∧ lastObs = (p, (v_inner, w)) := by
      have hlen : init_rev.reverse.length = κ_inner.length := by
        have h : (init_rev.reverse ++ [lastObs]).length =
                 (κ_inner ++ [(p, (v_inner, w))]).length :=
          congrArg List.length hκ_eq
        simp only [List.length_append, List.length_cons, List.length_nil] at h
        omega
      have ⟨h1, h2⟩ := List.append_inj hκ_eq hlen
      refine ⟨h1.symm, ?_⟩
      have := List.cons_eq_cons.mp h2
      exact this.1
    subst hκ_inner_eq; subst hlast_eq; subst he₂_eq
    -- Now apply the inner WP step continuation to the inner base step. The
    -- shape `={∅}▷=∗^[n+1] |={∅,E}=> X` for n=0 unfolds to
    -- `|={∅}=∗ ▷ |={∅,E}=> X` (matching the surrounding goal shape).
    have Hprim_e : PrimStep.primStep (e, σ₁) init_rev.reverse
        (Exp.val v_inner, σ₂, eₜ) :=
      EctxLanguage.primStep_of_baseStep Hbase_e
    ispecialize HWPe $$ %_ %_ %_ %Hprim_e Hcred
    -- HWPe : ={∅}▷=∗^[n+1] |={∅,E}=> X_inner. Goal: ={∅}▷=∗^[n+1] |={∅,E}=> Y_outer.
    -- Bridge them via `step_fupdN_wand`.
    iapply step_fupdN_wand $$ HWPe
    iintro HWPe
    imod HWPe with ⟨Hσ_post, HWPval, Hefs⟩
    icases (stateInterp_split σ₂ (ns + 1) ((p, (v_inner, w)) :: obs') (nt + eₜ.length)).mp
      $$ Hσ_post with ⟨Hheap_e, Hpmap_e⟩
    -- HWPval : WP (Val v_inner) {{ strong-post }}; convert to `|={E}=> strong-post v_inner`.
    ihave HWPval := wp_value_fupd'.mp $$ HWPval
    imod HWPval with ⟨%pvs', Hele, HΦ⟩
    -- The prophMapInterp now sees `(p, (v_inner, w)) :: obs'` at σ₂. Use
    -- `ProphMap.resolve_proph` to consume the front observation.
    icombine Hpmap_e Hele as Hcomb
    imod (ProphMap.resolve_proph (F := PNat) (V := Val × Val) (H := ProphMapF)
            p (v_inner, w) obs' σ₂.usedProphId pvs') $$ Hcomb
      with ⟨%pvs'', %hpvs'_eq, Hpmap_e, Hele⟩
    imodintro
    isplitl [Hheap_e Hpmap_e]
    · iapply (stateInterp_split σ₂ (ns + 1) obs' (nt + eₜ.length)).mpr
      iframe Hheap_e
      iexact Hpmap_e
    isplitr [Hefs]
    · iapply wp_value'
      iapply HΦ $$ %pvs'' %hpvs'_eq Hele
    · iexact Hefs

end Lifting

end Iris.HeapLang
