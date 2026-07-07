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

open Iris ProgramLogic Language.Notation Std FromMathlib

section HeapLangGS

abbrev HeapF := fun V => Std.ExtTreeMap Loc V compare

abbrev ProphMapF := fun V => Std.ExtTreeMap ProphId V compare

class HeapLangGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGpreS GF where
  heap_pre : genHeapPreS Loc (Option Val) GF HeapF
  proph_pre : prophMapPreS ProphId (Val × Val) GF ProphMapF

attribute [reducible, instance] HeapLangGpreS.heap_pre
attribute [reducible, instance] HeapLangGpreS.proph_pre

class HeapLangGS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGS_gen hlc GF where
  heap : genHeapGS Loc (Option Val) GF HeapF
  proph : prophMapGS ProphId (Val × Val) GF ProphMapF

attribute [reducible, instance] HeapLangGS.heap
attribute [reducible, instance] HeapLangGS.proph

instance HeapLangState [HeapLangGS hlc GF] : StateInterp State Observation GF where
  stateInterp σ _ κs _ := iprop% genHeapInterp σ.heap ∗ prophMapInterp κs σ.usedProphId

theorem stateInterp_split [HeapLangGS hlc GF] (σ : State) (ns : Nat)
    (κs : List Observation) (nt : Nat) : iprop%
    stateInterp σ ns κs nt ⊣⊢ genHeapInterp σ.heap ∗ prophMapInterp κs σ.usedProphId :=
  .rfl

theorem prophMapInterp_nil_append [HeapLangGS hlc GF] (κs : List Observation)
    (ps : Std.ExtTreeSet ProphId) : prophMapInterp ([] ++ κs) ps ⊣⊢ prophMapInterp κs ps :=
  .rfl

instance HeapLang [HeapLangGS hlc GF] : IrisGS_gen hlc Exp GF where
  numLatersPerStep n := 0
  forkPost v := iprop(True)
  stateInterp_mono σ ns obs nt := by iintro $

theorem state_interp_step [HeapLangGS hlc GF] (σ : State) (ns : Nat)
    (κs : List Observation) (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt ⊢ |==> stateInterp σ (ns + 1) κs nt := bupd_intro

def HeapLangS : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Loc (Agree (DiscreteO (Option Val))) HeapF), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Loc (Agree (DiscreteO GName)) HeapF), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | 7 => ⟨constOF (HeapView ProphId (Agree (DiscreteO (List (Val × Val)))) ProphMapF),
          by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instHeapLangGS_HeapLangS : HeapLangGpreS HasLC.hasLC HeapLangS where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6
  proph_pre := by
    constructor
    · constructor
      exists 7

end HeapLangGS

section Adequacy

theorem heap_adequacy [HeapLangGpreS .hasLC GF] (e : Exp) σ (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC GF], ⊢@{IProp GF} (WP e {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck e σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) .NotStuck e σ φ ?_
  intro inst κs
  imod iOwn_alloc (E := GhostMapG.elem (K := Loc) (V := Option Val) (H := HeapF))
    (HeapView.Auth (H := HeapF) (.own 1)
      (Std.PartialMap.map (fun v : Option Val => toAgree (DiscreteO.mk v)) σ.heap))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem (K := Loc) (V := GName) (H := HeapF))
    (HeapView.Auth (H := HeapF) (.own 1)
      (Std.PartialMap.map (fun g : GName => toAgree (DiscreteO.mk g))
        (∅ : HeapF GName)))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  imod (ProphMap.init (H := ProphMapF) κs σ.usedProphId) with ⟨%Gproph, Hproph⟩
  letI instHeapLangGS : HeapLangGS .hasLC GF := ⟨⟨γh, γm⟩, Gproph⟩
  imodintro
  iexists (fun σ κs => iprop% Iris.genHeapInterp σ.heap ∗ Iris.prophMapInterp κs σ.usedProphId)
  iexists (fun _ => iprop(True))
  simp only []
  -- NOTE: iframe %(@Hwp _) does not work here
  ihave #Hwp := (@Hwp _)
  iframe Hwp Hproph
  simp only [Iris.genHeapInterp]
  iexists (∅ : HeapF GName)
  unfold ghost_map_auth
  iframe Hh Hm
  ipureintro
  intro k hk
  simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk

end Adequacy

section Lifting

variable {GF : BundledGFunctors} {hlc : HasLC}
variable [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}

open EctxLanguage

theorem wp_rec {f x : Binder} {e : Exp} {vf v : Val}
    (h : vf = (.rec_ f x e)) :
    ▷ WP ((e.subst f vf).subst x v) @ s; E {{ Φ }}
    ⊢ WP hl(&vf &v) @ s; E {{ Φ }} := by
  iintro Hwp; subst h
  iapply wp_pure_step_fupd (Hφ := True.intro)
  dsimp only [Nat.repeat]
  iintro !> !> !> -; iframe

theorem wp_fork {e : Exp} :
    ▷ Φ (hl_val(#())) -∗
    ▷ WP e @ s; ⊤ {{ _v, True }} -∗
    WP hl(fork(&e)) @ s; E {{ Φ }} := by
  iintro HΦ Hwp
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  have Hred : BaseStep.Reducible (hl(fork(&e)), σ₁) :=
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
    iframe
  isplitr [Hwp]
  · iexists _
    iframe HΦ
    ipureintro; rfl
  · iapply BI.BigSepL.bigSepL_singleton
    iframe Hwp

theorem wp_fork_fupd {e : Exp} :
    (▷ |={E}=> (WP e @ s; ⊤ {{ _v, True }} ∗ Φ (hl_val(#())))) ⊢
      WP hl(fork(&e)) @ s; E {{ Φ }} := by
  iintro HeΦ
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  have Hred : BaseStep.Reducible (hl(fork(&e)), σ₁) :=
    ⟨[], hl(#BaseLit.unit), σ₁, [e], by constructor⟩
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
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

theorem wp_alloc (v : Val) (Φ : Val → IProp GF ) :
    ▷ (∀ l : Loc, l ↦ some v -∗ Φ (.lit $ .loc l)) -∗
    WP hl(ref(&v)) @ s; E {{ Φ }} := by
  iintro HΦ
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  let l := (List.fresh σ₁.heap.keys).choose
  have Hne : σ₁.get? l = .none := by
    simpa [State.get?, get?, getElem?_eq_none_iff, ←Std.ExtTreeMap.mem_keys]
      using (List.fresh σ₁.heap.keys).choose_spec
  have Hred : BaseStep.Reducible (hl(ref(&v)), σ₁) := by
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
  iapply HΦ $$ [$]

theorem wp_load {l : Loc} {q} {v : Val} Φ :
    ▷ l ↦{q} some v -∗
    ▷ (l ↦{q} some v -∗ Φ v) -∗
    WP hl(!v(#l)) @ s; E {{ Φ }} := by
  iintro >Hpt HΦ
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  ihave %Hpt : ⌜σ₁.get? l = v⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(!#l), σ₁)⌝ $$ []
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
  iexists _; isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ [$]

theorem wp_store {l : Loc} {v v' : Val} Φ :
    ▷ l ↦ some v' -∗
    ▷ (l ↦ some v -∗ Φ hl_val(#())) -∗
    WP hl(v(#l) ← &v) @ s; E {{ Φ }} := by
  iintro >Hpt HΦ
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(#l ← &v), σ₁)⌝ $$ []
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
  isplit
  · ipureintro; rfl
  · iapply HΦ $$ [$]

theorem wp_cmpXchg_fail {l : Loc} {q} {v' : Val} {e1 : Exp} {v1 : Val} {e2 : Exp} {v2 : Val}
    (Heq1 : toVal e1 = .some v1) (Heq2 : toVal e2 = .some v2) (Heq3 : v'.compareSafe v1)
    (Heq4 : decide (v' = v1) = false) :
      ▷ (l ↦{q} some v')
      ⊢ (WP hl(cmpXchg(v(#l), &e1, &e2)) @ s; E
          {{ v'', ⌜v'' = hl_val((&v', #false))⌝ ∗ l ↦{q} some v' }}) := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(cmpXchg(v(#l), &e1, &e2)), σ₁)⌝ $$ []
  · ipureintro
    exists [], hl(v((&v', #false))), σ₁, []
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
  simp only [Algebra.BigOpL.bigOpL_nil]
  subst Heq4; simp only [toVal] at Heq1 Heq2
  obtain ⟨rfl⟩ := Heq1
  obtain ⟨rfl⟩ := Heq2
  simp only [Heq4, Bool.false_eq_true, ↓reduceIte]
  imodintro
  simp only [toVal_coe, Option.some.injEq, stateInterp]
  iframe Hσ Hproph
  isplit <;> try itrivial
  iexists hl_val((&v', #false))
  iframe Hpt
  ipureintro
  simp

theorem wp_cmpXchg_true {l : Loc} {v' : Val} {e1 : Exp} {v1 : Val} {e2 : Exp} {v2 : Val}
    (Heq1 : toVal e1 = .some v1) (Heq2 : toVal e2 = .some v2) (Heq3 : v'.compareSafe v1)
    (Heq4 : decide (v' = v1) = true) :
      ▷ (l ↦ some v')
      ⊢ WP hl(cmpXchg(v(#l), &e1, &e2)) @ s; E
        {{ v'', ⌜v'' = hl_val((&v', #true))⌝ ∗ l ↦ some v2 }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(cmpXchg(v(#l), &e1, &e2)), σ₁)⌝ $$ []
  · ipureintro
    exists [], hl(v((&v', #true))), (σ₁.initHeap l 1 (some v2)), []
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
  subst Heq4; simp only [toVal] at Heq1 Heq2
  obtain ⟨rfl⟩ := Heq1
  obtain ⟨rfl⟩ := Heq2
  simp only [Heq4, ↓reduceIte, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := .some v2) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ Hproph
  isplit <;> try itrivial
  iexists hl_val((&v', #true))
  iframe Hpt
  ipureintro; simp [toVal]
  rfl

theorem wp_free {l : Loc} {v : Val} :
    ▷ (l ↦ some v) ⊢ WP hl(free(#l)) @ s; E {{ v'', ⌜v'' = hl_val(#())⌝ ∗ l ↦ none }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(free(#l)), σ₁)⌝ $$ []
  · ipureintro
    exists [], hl_val(#()), σ₁.initHeap l 1 none, []
    refine BaseStep.freeS l v _ ?_
    grind
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  rcases baseStep_of_primStep_of_baseStep_reducible Hred Heq with ⟨v'', H⟩
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil, Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := none) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ Hproph
  isplit <;> try itrivial
  iexists hl_val(#())
  iframe Hpt
  ipureintro
  simp [toVal]
  rfl

theorem wp_xchg {l : Loc} {v w : Val} :
    ▷ (l ↦ some v) ⊢ WP hl(xchg(#l, &w)) @ s; E {{ v'', ⌜v'' = v⌝ ∗ l ↦ some w }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(xchg(#l, &w)), σ₁)⌝ $$ []
  · ipureintro
    exists [], .val v, (σ₁.initHeap l 1 w), []
    refine BaseStep.xchgS l v w _ ?_; grind
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  rcases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i v1' H
  obtain rfl : v = v1' := by
    simp only [Hpt, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
    exact H
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil, Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := some w) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ Hproph
  isplit <;> try itrivial
  iexists v
  iframe Hpt
  ipureintro; simp [toVal]; rfl

theorem wp_faa {l : Loc} {i1 i2 : Int} :
    ▷ (l ↦ some hl_val(#i1))
    ⊢ WP hl(faa(#l, #i2)) @ s; E {{ v'', ⌜v'' = hl_val(#i1)⌝ ∗ l ↦ some hl_val(#(i1 + i2)) }} := by
  iintro >Hpt
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  ihave %Hpt : ⌜σ₁.get? l = .some (.some (Val.lit (.int i1)))⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%Heq'
    itrivial
  ihave %Hred : ⌜BaseStep.Reducible (hl(faa(#l, #i2)), σ₁)⌝ $$ []
  · ipureintro
    exists [], (.val (.lit (.int i1))), (σ₁.initHeap l 1 (some hl_val(#(i1 + i2)))), []
    refine BaseStep.faaS l i1 i2 _ ?_; grind
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  iintro !> %e₂ %σ₂ %eₜ %Heq Hcr
  cases baseStep_of_primStep_of_baseStep_reducible Hred Heq
  rename_i i1' H
  obtain rfl : i1 = i1' := by
    simp only [Hpt, Option.some.injEq, Val.lit.injEq, BaseLit.int.injEq] at H
    exact H
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  simp only [stateInterp, Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil, Algebra.BigOpL.bigOpL_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := some hl_val(#(i1 + i2))) $$ [$Hσ $Hpt]
    with ⟨Hσ, Hpt⟩
  imodintro
  iframe Hσ Hproph
  isplit <;> try itrivial
  iexists Val.lit (.int i1)
  iframe Hpt
  ipureintro; simp [toVal]; rfl

theorem wp_new_proph :
    ⊢ WP hl(newProph()) @ s; E {{ v, ∃ p, ∃ pvs, ⌜v = .lit (.prophecy p)⌝ ∗ proph p pvs }} := by
  iapply wp_lift_atomic_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
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
  have Hp'_mem : p' ∉ σ₁.usedProphId :=
    fun hmem => Hp' (Std.ExtTreeSet.mem_iff_contains.symm.mp hmem)
  imod ProphMap.new_proph p' σ₁.usedProphId obs' Hp'_mem $$ Hproph with ⟨Hproph', Htok⟩
  imodintro
  simp only [stateInterp]
  iframe Hσ
  isplitl [Hproph']
  · rw [show σ₁.usedProphId.insert p' = {p'} ∪ σ₁.usedProphId by
        ext x; simp [Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.mem_union_iff]]
    iexact Hproph'
  isplitl [Htok]
  · iexists hl_val(#(BaseLit.prophecy p'))
    isplit
    · ipureintro; simp [toVal]; rfl
    iexists p', _
    iframe Htok
    ipureintro; rfl
  · simp only [Algebra.BigOpL.bigOpL_nil]; itrivial

theorem wp_resolve_strong {e : Exp} {p : ProphId} {w : Val} {pvs : List (Val × Val)}
    (hatom : Language.Atomic Language.Atomicity.StronglyAtomic e) (hne : toVal e = none) :
    proph p pvs -∗
    (proph p pvs -∗ WP e @ s; E {{ v_e, ∃ pvs', proph p pvs' ∗
      ∀ pvs'', ⌜pvs' = (v_e, w) :: pvs''⌝ -∗ proph p pvs'' -∗ Φ v_e }}) -∗
    WP hl(resolve(&e, v(#p), v(&w))) @ s; E {{ Φ }} := by
  iintro Hp HWPe
  iapply wp_lift_step_fupdN rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hheap, Hpmap⟩
  icases ProphMap.agree (obs ++ obs') σ₁.usedProphId p pvs $$ [$Hpmap $Hp] with %Hagree
  have hredR : Stuckness.MaybeReducible s (e, σ₁) →
      Stuckness.MaybeReducible s (hl(resolve(&e, v(#p), v(&w))), σ₁) := fun Hred_e => by
    cases s <;> simp only [Stuckness.MaybeReducible] at Hred_e ⊢
    refine prim_step_reducible_resolve ?_ Hred_e
    exact Std.ExtTreeSet.mem_iff_contains.mp Hagree.1
  ihave HWPe : iprop(WP e @ s; E {{ v_e, ∃ pvs', proph p pvs' ∗
      ∀ pvs'', ⌜pvs' = (v_e, w) :: pvs''⌝ -∗ proph p pvs'' -∗ Φ v_e }}) $$ [Hp HWPe]
  · iapply HWPe; iexact Hp
  ihave HWPe := (show iprop(WP e @ s; E {{ v_e, ∃ pvs', proph p pvs' ∗
      ∀ pvs'', ⌜pvs' = (v_e, w) :: pvs''⌝ -∗ proph p pvs'' -∗ Φ v_e }}) ⊢ _
    by rw [wp_unfold.to_eq]; simp only [wp.pre, hne]; exact .rfl) $$ HWPe
  cases obs using List.reverseRec with
  | nil =>
    ihave Hσ_e : iprop(stateInterp σ₁ ns ([] ++ obs') nt) $$ [Hheap Hpmap]
    · iapply (stateInterp_split σ₁ ns ([] ++ obs') nt).mpr; iframe Hheap; iexact Hpmap
    imod HWPe $$ %_ %_ %_ %_ %_ Hσ_e with ⟨%Hred_e, _⟩
    imodintro
    isplitr
    · ipureintro; exact hredR Hred_e
    iintro %e₂ %σ₂ %eₜ %Hstep _
    exfalso
    obtain ⟨_, _, hκ_eq, _, _⟩ := step_resolve_decompose Hstep
    exact List.cons_ne_nil _ _ (List.append_eq_nil_iff.mp hκ_eq.symm).2
  | append_singleton init lastObs ih =>
    clear ih
    have hassoc : (init ++ [lastObs]) ++ obs' = init ++ (lastObs :: obs') := by simp
    ihave Hσ_e : iprop(stateInterp σ₁ ns (init ++ (lastObs :: obs')) nt) $$ [Hheap Hpmap]
    · iapply (stateInterp_split σ₁ ns (init ++ (lastObs :: obs')) nt).mpr
      iframe Hheap; rw [← hassoc]; iexact Hpmap
    imod HWPe $$ %_ %_ %_ %_ %_ Hσ_e with ⟨%Hred_e, HWPe⟩
    imodintro
    isplitr
    · ipureintro; exact hredR Hred_e
    iintro %e₂ %σ₂ %eₜ %Hstep Hcred
    obtain ⟨κ_inner, v_inner, hκ_eq, rfl, Hbase_e⟩ := step_resolve_decompose Hstep
    obtain ⟨rfl, rfl⟩ := (by simpa using congrArg List.reverse hκ_eq : lastObs = _ ∧ init = κ_inner)
    ispecialize HWPe $$ %_ %_ %_ %(EctxLanguage.primStep_of_baseStep Hbase_e) Hcred
    iapply step_fupdN_wand $$ HWPe
    iintro HWPe
    imod HWPe with ⟨Hσ_post, HWPval, Hefs⟩
    icases (stateInterp_split σ₂ (ns + 1) ((p, (v_inner, w)) :: obs') (nt + eₜ.length)).mp
      $$ Hσ_post with ⟨Hheap_e, Hpmap_e⟩
    imod wp_value_fupd'.mp $$ HWPval with ⟨%pvs', Hele, HΦ⟩
    icombine Hpmap_e Hele as Hcomb
    imod (ProphMap.resolve_proph p (v_inner, w) obs' σ₂.usedProphId pvs') $$ Hcomb
      with ⟨%pvs'', %hpvs'_eq, Hpmap_e, Hele⟩
    imodintro
    iframe
    isplitl [Hheap_e Hpmap_e]
    · iapply (stateInterp_split σ₂ (ns + 1) obs' (nt + eₜ.length)).mpr $$ [$]
    iapply wp_value'
    iapply HΦ $$ %pvs'' %hpvs'_eq Hele

theorem wp_resolve {e : Exp} {p : ProphId} {w : Val} {pvs : List (Val × Val)}
    (hatom : Language.Atomic Language.Atomicity.StronglyAtomic e) (hne : toVal e = none) :
    proph p pvs -∗
    WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, w) :: pvs'⌝ -∗ proph p pvs' -∗ Φ r }} -∗
    WP hl(resolve(&e, v(#p), v(&w))) @ s; E {{ Φ }} := by
  iintro Hp WPe
  iapply wp_resolve_strong hatom hne $$ Hp
  iintro Hp
  iapply wp_wand $$ WPe
  iintro %r Hcont
  iexists pvs
  iframe Hp
  iexact Hcont

end Lifting

end Iris.HeapLang
