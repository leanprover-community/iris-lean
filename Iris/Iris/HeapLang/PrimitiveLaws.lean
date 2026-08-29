/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang.Syntax
public import Iris.HeapLang.Semantics
public import Iris.HeapLang.Notation
public import Iris.HeapLang.Instances
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.TotalWeakestPre
public import Iris.ProgramLogic.Adequacy
public import Iris.ProgramLogic.TotalEctxLifting
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

abbrev ProphMapF := fun V => Std.ExtTreeMap ProphId V compare

@[rocq_alias heap_lang.heapGpreS]
class HeapLangGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) extends InvGpreS GF where
  heap_pre : genHeapPreS Loc (Option Val) GF HeapF
  proph_pre : prophMapPreS ProphId (Val × Val) GF ProphMapF

attribute [reducible, instance] HeapLangGpreS.heap_pre
attribute [reducible, instance] HeapLangGpreS.proph_pre

#rocq_ignore heap_lang.«heapΣ» "Superseded by the `HeapLangGpreS` typeclass on `BundledGFunctors`."
#rocq_ignore heap_lang.subG_heapGpreS "Superseded by Lean's direct `ElemG` typeclass synthesis."

/-! ### The heap_lang points-to assertion
The HeapLang points-to assertion is taken from `gen_heap`. -/

attribute [rocq_alias heap_lang.pointsto] pointsTo
attribute [rocq_alias heap_lang.pointsto_timeless] instTimelessPointsTo
attribute [rocq_alias heap_lang.pointsto_fractional] instFractionalPointsTo
attribute [rocq_alias heap_lang.pointsto_as_fractional] instAsFractionalPointsTo
attribute [rocq_alias heap_lang.pointsto_valid] pointsTo_cmraValid
attribute [rocq_alias heap_lang.pointsto_valid_2] pointsTo_op_cmraValid
attribute [rocq_alias heap_lang.primitive_laws.pointsto_agree] pointsTo_agree
attribute [rocq_alias heap_lang.primitive_laws.pointsto_combine] pointsTo_combine
attribute [rocq_alias heap_lang.pointsto_frac_ne] pointsTo_frac_ne
attribute [rocq_alias heap_lang.pointsto_ne] pointsTo_ne
attribute [rocq_alias heap_lang.pointsto_persist] pointsTo_persist
attribute [rocq_alias heap_lang.pointsto_unpersist] pointsTo_unpersist
attribute [rocq_alias heap_lang.pointsto_persistent] instPersistentPointsTo

#rocq_ignore heap_lang.pointsto_def "Rocq sealing auxiliary definition."
#rocq_ignore heap_lang.pointsto_aux "Rocq sealing auxiliary definition."
#rocq_ignore heap_lang.pointsto_unseal "Rocq unsealing lemma."

@[rocq_alias heap_lang.heapGS_gen]
class HeapLangGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  -- not an instance on purpose to avoid diamonds with IrisGS_gen
  [invGS : InvGS_gen hlc GF]
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

@[rocq_alias heap_lang.heapGS_irisGS]
instance HeapLang [HeapLangGS hlc GF] : IrisGS_gen hlc Exp GF where
  invGS := HeapLangGS.invGS
  numLatersPerStep n := 0
  forkPost v := iprop(True)
  stateInterp_mono σ ns obs nt := by
    let := @HeapLangGS.invGS hlc GF _
    iintro $

theorem state_interp_step [HeapLangGS hlc GF] (σ : State) (ns : Nat)
    (κs : List Observation) (nt : Nat) :
    stateInterp (GF := GF) σ ns κs nt ⊢ |==> stateInterp σ (ns + 1) κs nt := bupd_intro

def HeapLangS : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
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

@[rocq_alias heap_lang.heap_adequacy]
theorem heap_adequacy [HeapLangGpreS .hasLC GF] (e : Exp) σ (φ : Val → Prop)
    (Hwp : ∀ [HeapLangGS .hasLC GF], ⊢@{IProp GF} (WP e {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck e σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) .NotStuck e σ φ ?_
  intro inst κs
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (H := HeapF) (.own 1)
      (Std.PartialMap.map (fun v : Option Val => toAgree (DiscreteO.mk v)) σ.heap))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem) (HeapView.Auth (H := HeapF) (.own 1)
      (Std.PartialMap.map (fun g : GName => toAgree (DiscreteO.mk g)) (∅ : HeapF GName)))
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

@[rocq_alias heap_lang.wp_fork_fupd]
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

@[rocq_alias heap_lang.wp_fork]
theorem wp_fork {e : Exp} :
    ▷ Φ (hl_val(#())) -∗
    ▷ WP e @ s; ⊤ {{ _v, True }} -∗
    WP hl(fork(&e)) @ s; E {{ Φ }} := by
  iintro HΦ Hwp
  iapply wp_fork_fupd
  inext
  imodintro
  iframe

/-! ## Multi-cell allocation -/

@[rocq_alias heap_lang.heap_array_to_seq_pointsto]
theorem allocCells_toSeq_pointsTo {l : Loc} {v : Val} {n : Nat} :
    ([∗map] l' ↦ ov ∈ allocCells l n v, l' ↦ ov) ⊢
      [∗list] i ∈ List.range n, l + i ↦ v := by
  induction n with
  | zero => exact BI.BigSepM.bigSepM_empty.1.trans BI.BigSepL.bigSepL_nil.2
  | succ n ih =>
    rw [allocCells_succ, List.range_succ]
    refine (BI.BigSepM.bigSepM_insert get?_allocCells_self).1.trans ?_
    refine .trans ?_ BI.BigSepL.bigSepL_snoc.2
    exact BI.sep_comm.1.trans (BI.sep_mono ih .rfl)

@[rocq_alias heap_lang.heap_array_to_seq_meta]
theorem heapArray_toSeq_metaToken {l : Loc} {vs : List (Option Val)} {n : Nat}
    (hlen : vs.length = n) :
    ([∗map] l' ↦ _ov ∈ heapArray l vs, metaToken l' ⊤) ⊢
      [∗list] i ∈ List.range n, metaToken (l + i) ⊤ := by
  subst n
  induction vs using List.reverseRec generalizing l with
  | nil => exact BI.BigSepM.bigSepM_empty.1.trans BI.BigSepL.bigSepL_nil.2
  | append_singleton vs v ih =>
    rw [heapArray_snoc, List.length_append, List.length_singleton, Nat.add_one, List.range_succ]
    refine (BI.BigSepM.bigSepM_insert (Φ := fun l' _ => iprop(metaToken l' ⊤))
      get?_heapArray_self).1.trans ?_
    refine .trans ?_ BI.BigSepL.bigSepL_snoc.2
    exact BI.sep_comm.1.trans (BI.sep_mono ih .rfl)

@[rocq_alias heap_lang.twp_allocN_seq]
theorem twp_allocN_seq {v : Val} {n : Int} (hn : 0 < n) :
    [{ True }] hl(allocn(#n, &v)) @ s; E
    [{ l, RET hl_val(#(.loc l));
        ([∗list] i ∈ List.range n.toNat, (l + i) ↦ some v ∗ metaToken (l + i) ⊤) }] := by
  iintro %Φ - HΦ
  iapply twp.lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %nt ⟨Hσ, Hobs⟩ !>
  obtain ⟨l, hfresh⟩ := exists_fresh_block σ₁.heap n
  isplit
  · ipureintro
    exact ⟨.ofVal (.lit (.loc l)), σ₁.initHeap l n v, [], .allocNS n v σ₁ l hn hfresh⟩
  iintro %ob %v₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i l' _hn' hfresh'
  imod genHeap_alloc_big (allocCells l' n.toNat v) σ₁.heap (allocCells_disjoint hfresh') $$ Hσ
    with ⟨Hσ, Hpts, Htok⟩
  imodintro
  isplit
  · itrivial
  isplit
  · itrivial
  ihave Hσ := genHeapInterp_eqv (.symm _ _ initHeap_heap_eq) $$ Hσ
  isimp only []
  iframe Hσ Hobs
  iexists hl_val(#(BaseLit.loc _))
  isplit; ipureintro; rfl
  iapply HΦ
  iapply BI.BigSepL.bigSepL_sep_eqv.2
  isplitl [Hpts]
  · iapply allocCells_toSeq_pointsTo $$ Hpts
  · iapply heapArray_toSeq_metaToken $$ Htok
    grind

@[rocq_alias heap_lang.wp_allocN_seq]
theorem wp_allocN_seq (v : Val) {n : Int} (hn : 0 < n) :
    {{ True }} hl(allocn(#n, &v)) @ s; E
    {{ l, RET hl_val(#(.loc l));
        ([∗list] i ∈ List.range n.toNat, (l + i) ↦ some v ∗ metaToken (l + i) ⊤) }} := by
  iintro %Φ _ HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_allocN_seq hn
  · itrivial
  iintro %l H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.wp_alloc]
theorem wp_alloc (v : Val) :
    {{ True }} hl(ref(&v)) @ s; E {{ l, RET hl_val(#l); l ↦ some v }} := by
  iintro %Φ _ HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_allocN_seq (by omega)
  · itrivial
  iintro %l H HΦ
  ihave Hpt : iprop(l ↦ some v) $$ [H]
  · rw [Int.toNat_one, List.range_one, BI.BigSepL.bigSepL_singleton.to_eq]
    rw [show l + 0 = l from loc_add_zero l]
    exact BI.sep_elim_left
  iapply HΦ $$ Hpt

@[rocq_alias heap_lang.twp_load]
theorem twp_load {l : Loc} {q} {v : Val} :
    [{ l ↦{q} some v }] hl(!v(#l)) @ s; E [{ RET v; l ↦{q} some v }] := by
  iintro %Φ Hpt HΦ
  iapply twp.lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %nt ⟨Hσ, Hobs⟩ !>
  ihave %Hpt : ⌜σ₁.get? l = v⌝ $$ [Hσ Hpt]
  · ihave >%_ := genHeap_valid $$ [$Hσ $Hpt]
    itrivial
  isplit
  · ipureintro
    exact ⟨.val v, σ₁, [], by constructor; simp [Hpt]⟩
  iintro %κ %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i v' H
  rw [Hpt] at H
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
  subst H
  imodintro
  isplit; itrivial
  isplit; itrivial
  iframe Hσ Hobs
  iexists v
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

@[rocq_alias heap_lang.wp_load]
theorem wp_load {l : Loc} {q} {v : Val} :
    {{ ▷ l ↦{q} some v }} hl(!v(#l)) @ s; E {{ RET v; l ↦{q} some v }} := by
  iintro %Φ >Hpt HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_load $$ Hpt
  iintro Hpt HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_store]
theorem twp_store {l : Loc} {v v' : Val} :
    [{ l ↦ some v' }] hl(v(#l) ← &v) @ s; E [{ RET hl_val(#()); l ↦ some v }] := by
  iintro %Φ Hpt HΦ
  iapply twp.lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %nt ⟨Hσ, Hobs⟩ !>
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%_
    itrivial
  isplit
  · ipureintro
    refine ⟨.val (.lit .unit), σ₁.initHeap l 1 v, [], BaseStep.storeS _ v' _ _ ?_⟩
    grind
  iintro %κ %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i v'' H
  rw [Hpt] at H
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
  subst H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := .some v) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  isplit; itrivial
  iframe Hσ Hobs
  iexists hl_val(#())
  isplit
  · ipureintro; rfl
  · iapply HΦ $$ Hpt

@[rocq_alias heap_lang.wp_store]
theorem wp_store {l : Loc} {v v' : Val} :
    {{ ▷ l ↦ some v' }} hl(v(#l) ← &v) @ s; E {{ RET hl_val(#()); l ↦ some v }} := by
  iintro %Φ >Hpt HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_store $$ Hpt
  iintro Hpt HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_cmpxchg_fail]
theorem twp_cmpXchg_fail {l : Loc} {q} {v' v1 v2 : Val} (hne : v' ≠ v1) (hsafe : v'.compareSafe v1) :
    [{ l ↦{q} some v' }] hl(cmpXchg(#l, &v1, &v2)) @ s; E
      [{ RET hl_val((&v', #false)); l ↦{q} some v' }] := by
  iintro %Φ Hpt HΦ
  iapply twp.lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %nt ⟨Hσ, Hobs⟩ !>
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%_
    itrivial
  isplit
  · ipureintro
    refine ⟨hl(v((&v', #false))), σ₁, [], .cmpXchgS l v1 v2 v' σ₁ false Hpt hsafe ?_⟩
    simp [hne]
  iintro %κ %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i vl b _ Hdec Hget
  rw [Hpt] at Hget
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at Hget
  subst Hget
  have hb : b = false := by simpa [hne] using Hdec.symm
  subst b
  imodintro
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  isplit; itrivial
  isplit; itrivial
  iframe Hσ Hobs
  iexists hl_val((&v', #false))
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

@[rocq_alias heap_lang.wp_cmpxchg_fail]
theorem wp_cmpXchg_fail {l : Loc} {q} {v' : Val} {e1 : Exp} {v1 : Val} {e2 : Exp} {v2 : Val}
    (Heq1 : toVal e1 = .some v1) (Heq2 : toVal e2 = .some v2) (Heq3 : v'.compareSafe v1)
    (Heq4 : decide (v' = v1) = false) :
    {{ ▷ l ↦{q} some v' }} hl(cmpXchg(v(#l), &e1, &e2)) @ s; E
    {{ RET hl_val((&v', #false)); l ↦{q} some v' }} := by
  rw [show e1 = ToVal.ofVal v1 by grind, show e2 = ToVal.ofVal v2 by grind]
  iintro %Φ >Hpt HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_cmpXchg_fail (by grind) Heq3 $$ Hpt
  iintro Hpt HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_cmpxchg_suc]
theorem twp_cmpXchg_true {l : Loc} {v' v1 v2 : Val}
    (heq : v' = v1) (hsafe : v'.compareSafe v1) :
    [{ l ↦ some v' }] hl(cmpXchg(#l, &v1, &v2)) @ s; E
      [{ RET hl_val((&v', #true)); l ↦ some v2 }] := by
  iintro %Φ Hpt HΦ
  iapply twp.lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %nt ⟨Hσ, Hobs⟩ !>
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v')⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%_
    itrivial
  isplit
  · ipureintro
    refine ⟨hl(v((&v', #true))), σ₁.initHeap l 1 v2, [],
      .cmpXchgS l v1 v2 v' σ₁ true Hpt hsafe ?_⟩
    simp [heq]
  iintro %κ %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i vl b _ Hdec Hget
  rw [Hpt] at Hget
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at Hget
  subst Hget
  have hb : b = true := by simpa [heq] using Hdec.symm
  subst b
  simp only [hb, ↓reduceIte, Int.toNat_one, List.range_one, List.foldl_cons,
    Int.cast_ofNat_Int, List.foldl_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := .some v2) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  isplit; itrivial
  iframe Hσ Hobs
  iexists hl_val((&v', #true))
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

@[rocq_alias heap_lang.wp_cmpxchg_suc]
theorem wp_cmpXchg_true {l : Loc} {v' : Val} {e1 : Exp} {v1 : Val} {e2 : Exp} {v2 : Val}
    (Heq1 : toVal e1 = .some v1) (Heq2 : toVal e2 = .some v2) (Heq3 : v'.compareSafe v1)
    (Heq4 : decide (v' = v1) = true) :
    {{ ▷ l ↦ some v' }} hl(cmpXchg(v(#l), &e1, &e2)) @ s; E
    {{ RET hl_val((&v', #true)); l ↦ some v2 }} := by
  rw [show e1 = ToVal.ofVal v1 by grind, show e2 = ToVal.ofVal v2 by grind]
  iintro %Φ >Hpt HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_cmpXchg_true (by grind) Heq3 $$ Hpt
  iintro Hpt HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.wp_free]
theorem wp_free {l : Loc} {v : Val} :
    {{ ▷ l ↦ some v }} hl(free(#l)) @ s; E {{ RET hl_val(#()); l ↦ none }} := by
  iintro %Φ >Hpt HΦ
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
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ
    itrivial

@[rocq_alias heap_lang.twp_xchg]
theorem twp_xchg {l : Loc} {v w : Val} :
    [{ l ↦ some v }] hl(xchg(#l, &w)) @ s; E [{ RET v; l ↦ some w }] := by
  iintro %Φ Hpt HΦ
  iapply twp.lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %nt ⟨Hσ, Hobs⟩ !>
  ihave %Hpt : ⌜σ₁.get? l = .some (.some v)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%_
    itrivial
  isplit
  · ipureintro
    refine ⟨.val v, σ₁.initHeap l 1 w, [], .xchgS l v w σ₁ ?_⟩
    grind
  iintro %κ %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i v' H
  obtain rfl : v = v' := by
    simp only [Hpt, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at H
    exact H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := some w) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  isplit; itrivial
  iframe Hσ Hobs
  iexists v
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

@[rocq_alias heap_lang.wp_xchg]
theorem wp_xchg {l : Loc} {v w : Val} :
    {{ ▷ l ↦ some v }} hl(xchg(#l, &w)) @ s; E {{ RET v; l ↦ some w }} := by
  iintro %Φ >Hpt HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_xchg $$ Hpt
  iintro Hpt HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_faa]
theorem twp_faa {l : Loc} {i1 i2 : Int} :
    [{ l ↦ some hl_val(#i1) }] hl(faa(#l, #i2)) @ s; E
      [{ RET hl_val(#i1); l ↦ some hl_val(#(i1 + i2)) }] := by
  iintro %Φ Hpt HΦ
  iapply twp.lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %nt ⟨Hσ, Hobs⟩ !>
  ihave %Hpt : ⌜σ₁.get? l = .some (.some (Val.lit (.int i1)))⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%_
    itrivial
  isplit
  · ipureintro
    refine ⟨.val (.lit (.int i1)), σ₁.initHeap l 1 (some hl_val(#(i1 + i2))), [],
      .faaS l i1 i2 σ₁ ?_⟩
    grind
  iintro %κ %e₂ %σ₂ %efs %Hstep
  rcases Hstep
  rename_i i1' H
  obtain rfl : i1 = i1' := by
    simp only [Hpt, Option.some.injEq, Val.lit.injEq, BaseLit.int.injEq] at H
    exact H
  simp only [Int.toNat_one, List.range_one, List.foldl_cons, Int.cast_ofNat_Int,
    List.foldl_nil]
  rw [show l + (0 : Int) = l by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind]
  imod genHeap_update (v₂ := some hl_val(#(i1 + i2))) $$ [$Hσ $Hpt]
    with ⟨Hσ, Hpt⟩
  imodintro
  isplit; itrivial
  isplit; itrivial
  iframe Hσ Hobs
  iexists Val.lit (.int i1)
  isplit
  · ipureintro; simp [toVal]; rfl
  · iapply HΦ $$ Hpt

@[rocq_alias heap_lang.wp_faa]
theorem wp_faa {l : Loc} {i1 i2 : Int} :
    {{ ▷ l ↦ some hl_val(#i1) }} hl(faa(#l, #i2)) @ s; E
    {{ RET hl_val(#i1); l ↦ some hl_val(#(i1 + i2)) }} := by
  iintro %Φ >Hpt HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_faa $$ Hpt
  iintro Hpt HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.wp_new_proph]
theorem wp_new_proph :
    {{ True }} hl(newProph()) @ s; E
    {{ pvs p, RET hl_val(#p); proph p pvs }} := by
  iintro %Φ _ HΦ
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
  isplitl [HΦ Htok]
  · iexists hl_val(#(BaseLit.prophecy p'))
    isplit
    · ipureintro; simp [toVal]; rfl
    iapply HΦ $$ [$]
  · simp only [Algebra.BigOpL.bigOpL_nil]; itrivial

@[rocq_alias heap_lang.wp_resolve_strong]
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
    by rw [wp_unfold.to_eq]) $$ HWPe
  cases obs using List.reverseRec with
  | nil =>
    ihave Hσ_e : iprop(stateInterp σ₁ ns ([] ++ obs') nt) $$ [Hheap Hpmap]
    · iapply (stateInterp_split σ₁ ns ([] ++ obs') nt).mpr; iframe Hheap; iexact Hpmap
    simp only [wp.pre, hne]
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
    simp only [wp.pre, hne]
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

@[rocq_alias heap_lang.wp_resolve]
theorem wp_resolve {e : Exp} {p : ProphId} {w : Val} {pvs : List (Val × Val)}
    (hatom : Language.Atomic Language.Atomicity.StronglyAtomic e)
    (hne : toVal e = none := by decide) :
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
