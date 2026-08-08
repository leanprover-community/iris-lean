/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.BI.BigOp.BigSepSet
public import Iris.ProgramLogic.ThreadPool
public import Iris.ProgramLogic.AbstractWeakestPre
public import Iris.ProgramLogic.AbstractLangCompleteness
public import Iris.ProgramLogic.AbstractEctxLangCompleteness
public import Iris.Instances.Lib.CInvariants
public import Iris.Instances.Lib.GhostMap
public import Iris.ProofMode

/-! # HeapLang completeness

Note: this is not a port. Upstream Iris has no completeness proof, so there are
no `rocq_alias` annotations in this file. -/

@[expose] public section
namespace Iris.HeapLang

open Iris ProgramLogic Iris.BI Language Language.Notation Std

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF]

@[reducible] def heapCellPts (l : Loc) (vo : Option Val) : IProp GF :=
  match vo with
  | some _ => iprop(l ↦ vo)
  | none => iprop(emp)

instance instTimeless_heapCellPts (l : Loc) (vo : Option Val) :
    Timeless (heapCellPts (GF := GF) l vo) := by
  cases vo <;> infer_instance

@[reducible] def cellInv (k : Loc) (vo : Option Val) : IProp GF :=
  iprop(heapCellPts k vo ∗ metaToken k ⊤)

theorem pointsTo_heapCellPts (l : Loc) (vo : Option Val) :
    (l ↦ vo) ⊢ heapCellPts (GF := GF) l vo := by
  cases vo with
  | some v => exact .rfl
  | none => exact Affine.affine

/-- Predicate which asserts ownership over a complete HeapLang state -/
@[reducible] def heapInv (σ : State) : IProp GF := iprop%
    (bigSepM (M := HeapF) cellInv σ.heap) ∗
    ([∗set] p ∈ σ.usedProphId, ∃ pvs, proph p pvs)

instance instTimeless_heapInv (σ : State) : Timeless (heapInv (GF := GF) σ) := by
  infer_instance

abbrev baseCompletenessGoal (e₁ : Exp) (σ : State) (E : CoPset) : IProp GF := iprop%
  ((⌜Atomic Atomicity.StronglyAtomic e₁⌝ ∗
      ∀ (Φ : Val → IProp GF),
        (▷ ∀ κ v₂ σ' efs, ⌜PrimStep.primStep (e₁, σ) κ (ToVal.ofVal v₂, σ', efs)⌝ ==∗
          ((heapInv σ' -∗ Φ v₂) ∗
            [∗list] _i ↦ etp ∈ efs, WP etp @ Stuckness.NotStuck; ⊤ {{ _v, True }})) -∗
        WP e₁ @ Stuckness.NotStuck; E {{ v, Φ v }}) ∨
   (heapInv σ ∗
      ∀ (Φ : Val → IProp GF) (E₂ : CoPset),
        (▷ ∀ e₂ efs, (∀ σ₁, heapInv σ₁ ={E}=∗
            ∃ κ σ₁', ⌜PrimSteps e₁ σ₁ κ e₂ σ₁' efs⌝ ∗ heapInv σ₁') ={E₂}=∗
          WP e₂ @ Stuckness.NotStuck; E₂ {{ v, Φ v }} ∗
          [∗list] _i ↦ etp ∈ efs, WP etp @ Stuckness.NotStuck; ⊤ {{ _v, True }}) -∗
        WP e₁ @ Stuckness.NotStuck; E₂ {{ v, Φ v }}))

theorem wp_base_pure {e₁ e₂ : Exp} {φ : Prop} [hpe : Language.PureExec φ 1 e₁ e₂] (hφ : φ)
    (σ : State) (E : CoPset)
    (hbase : ∀ σ' : State, BaseStep e₁ σ' [] e₂ σ' []) :
    heapInv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro Hinv
  imodintro
  iright
  iframe Hinv
  iintro %Φ %E₂ H
  iapply wp_pure_step_later (Hexec := hpe) (Hφ := hφ)
  iintro !> -
  ihave Htraj : iprop(∀ σ₁, heapInv σ₁ ={E}=∗
      ∃ κ σ₁', ⌜PrimSteps e₁ σ₁ κ e₂ σ₁' []⌝ ∗ heapInv σ₁') $$ []
  · iintro %σ₁ Hinv₁
    imodintro
    iexists [], σ₁
    iframe Hinv₁
    ipureintro
    exact PrimSteps.once (EctxLanguage.primStep_of_baseStep (hbase σ₁))
  iapply fupd_wp
  imod H $$ Htraj with ⟨Hwp, _⟩
  imodintro
  iexact Hwp

theorem wp_base_atomic {e₁ : Exp} {v₂ : Val} (l : Loc) (vlive : Val) (vnew : Option Val)
    (σ : State) (E : CoPset)
    (hatom : Atomic Atomicity.StronglyAtomic e₁)
    (hcell : get? (M := HeapF) σ.heap l = some (some vlive))
    (hbase : ∀ σ'' : State, get? (M := HeapF) σ''.heap l = some (some vlive) →
        BaseStep e₁ σ'' [] (ToVal.ofVal v₂) (σ''.initHeap l 1 vnew) [])
    (hdet : ∀ {σ'' : State} {obs e' σ''' efs},
        get? (M := HeapF) σ''.heap l = some (some vlive) →
        BaseStep e₁ σ'' obs e' σ''' efs →
        obs = [] ∧ e' = (ToVal.ofVal v₂ : Exp) ∧ σ''' = σ''.initHeap l 1 vnew ∧ efs = []) :
    heapInv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro ⟨Hmap, Hproph_inv⟩
  imodintro
  ileft
  iframe %hatom
  iintro %Φ Hstep
  icases (BigSepM.bigSepM_insert_acc (M := HeapF) (Φ := cellInv) hcell) $$ Hmap
    with ⟨⟨Hpt, Hmeta⟩, Hclose⟩
  iapply wp_lift_atomic_step (EctxLanguage.val_stuck (hbase σ hcell))
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  ihave %hcell1 : ⌜get? (M := HeapF) σ₁.heap l = some (some vlive)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%hh
    itrivial
  isplitr
  · ipureintro
    simp only [Stuckness.MaybeReducible]
    exact EctxLanguage.primStep_reducible_of_baseStep_reducible
      ⟨[], _, _, [], hbase σ₁ hcell1⟩
  iintro !> %e₂ %σ₂ %eₜ %Hprim -
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    hdet hcell1 (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible
      ⟨[], _, _, [], hbase σ₁ hcell1⟩ Hprim)
  imod genHeap_update (v₂ := vnew) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hstep $$ [] with ⟨Hpost, _⟩
  · ipureintro
    exact EctxLanguage.primStep_of_baseStep (hbase σ hcell)
  imodintro
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  have hl0 : l + (0 : Int) = l := by
    cases l
    simp only [HAdd.hAdd, Loc.mk.injEq]
    grind
  simp only [stateInterp, State.initHeap, Int.toNat_one, List.range_one, List.foldl_cons,
    Int.cast_ofNat_Int, List.foldl_nil, hl0,
    Algebra.BigOpL.bigOpL_nil]
  iframe
  iexists v₂
  isplit; ipureintro; simp [toVal]; rfl
  iapply Hpost
  simp only [heapInv]
  iframe
  iapply Hclose
  unfold cellInv
  iframe
  iapply (pointsTo_heapCellPts l vnew); iexact Hpt

theorem wp_base_atomic_nochange {e₁ : Exp} {v₂ : Val} (l : Loc) (vlive : Val)
    (σ : State) (E : CoPset)
    (hatom : Atomic Atomicity.StronglyAtomic e₁)
    (hcell : get? (M := HeapF) σ.heap l = some (some vlive))
    (hbase : ∀ σ'' : State, get? (M := HeapF) σ''.heap l = some (some vlive) →
        BaseStep e₁ σ'' [] (ToVal.ofVal v₂) σ'' [])
    (hdet : ∀ {σ'' : State} {obs e' σ''' efs},
        get? (M := HeapF) σ''.heap l = some (some vlive) →
        BaseStep e₁ σ'' obs e' σ''' efs →
        obs = [] ∧ e' = (ToVal.ofVal v₂ : Exp) ∧ σ''' = σ'' ∧ efs = []) :
    heapInv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) :=
  wp_base_atomic l vlive (some vlive) σ E hatom hcell
    (fun σ'' h => by rw [State.initHeap_self h]; exact hbase σ'' h)
    (fun h hs => by
      obtain ⟨ho, he, hσ, hf⟩ := hdet h hs
      exact ⟨ho, he, hσ.trans (State.initHeap_self h).symm, hf⟩)

/-! ### Per-operation determinism facts -/

theorem loadS_det {l : Loc} {v : Val} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some v))
    (hs : BaseStep (.load (.val (.lit (.loc l)))) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal v : Exp) ∧ σ' = σ ∧ efs = [] := by
  cases hs with | loadS => grind

theorem storeS_det {l : Loc} {w : Val} {σ : State} {obs e' σ' efs}
    (hs : BaseStep (.store (.val (.lit (.loc l))) (.val w)) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.lit .unit) : Exp) ∧
      σ' = σ.initHeap l 1 (some w) ∧ efs = [] := by
  cases hs with | storeS => grind

theorem freeS_det {l : Loc} {σ : State} {obs e' σ' efs}
    (hs : BaseStep (.free (.val (.lit (.loc l)))) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.lit .unit) : Exp) ∧
      σ' = σ.initHeap l 1 none ∧ efs = [] := by
  cases hs with | freeS => grind

theorem xchgS_det {l : Loc} {v1 v2 : Val} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some v1))
    (hs : BaseStep (.xchg (.val (.lit (.loc l))) (.val v2)) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal v1 : Exp) ∧ σ' = σ.initHeap l 1 (some v2) ∧ efs = [] := by
  cases hs with | xchgS => grind

theorem faaS_det {l : Loc} {i1 i2 : Int} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some (Val.lit (.int i1))))
    (hs : BaseStep (.faa (.val (.lit (.loc l))) (.val (.lit (.int i2)))) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.lit (.int i1)) : Exp) ∧
      σ' = σ.initHeap l 1 (some (Val.lit (.int (i1 + i2)))) ∧ efs = [] := by
  cases hs with | faaS => grind

theorem cmpXchgS_det_true {l : Loc} {v1 v2 vl : Val} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some vl)) (htrue : decide (vl = v1) = true)
    (hs : BaseStep (.cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2)) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.pair vl (.lit (.bool true))) : Exp) ∧
      σ' = σ.initHeap l 1 (some v2) ∧ efs = [] := by
  cases hs with | cmpXchgS => grind

theorem cmpXchgS_det_false {l : Loc} {v1 v2 vl : Val} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some vl)) (hfalse : decide (vl = v1) = false)
    (hs : BaseStep (.cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2)) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.pair vl (.lit (.bool false))) : Exp) ∧
      σ' = σ ∧ efs = [] := by
  cases hs with | cmpXchgS => grind

theorem wp_baseCompletenessGoal (e₁ : Exp) (σ : State) (E : CoPset)
    (Hred : BaseStep.Reducible (e₁, σ)) :
    heapInv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro Hinv
  obtain ⟨κ, e', σ', efs, Hstep⟩ := Hred
  cases Hstep with
  | recS f x e σ =>
      iapply (wp_base_pure trivial σ E (.recS f x e)) $$ Hinv
  | pairS v1 v2 σ =>
      iapply (wp_base_pure trivial σ E (.pairS v1 v2)) $$ Hinv
  | injLS v σ =>
      iapply (wp_base_pure trivial σ E (.injLS v)) $$ Hinv
  | injRS v σ =>
      iapply (wp_base_pure trivial σ E (.injRS v)) $$ Hinv
  | betaS f x eb v2 e' σ h =>
      iapply (wp_base_pure trivial σ E (.betaS f x eb v2 _ · rfl)) $$ Hinv
  | unOpS op v v' σ h =>
      iapply (wp_base_pure (hpe := instPureExecUnOp) h σ E (.unOpS op v v' · h)) $$ Hinv
  | binOpS op v1 v2 v' σ h =>
      iapply (wp_base_pure (hpe := instPureExecBinOp) h σ E (.binOpS op v1 v2 v' · h)) $$ Hinv
  | ifTrueS et ee σ =>
      iapply (wp_base_pure trivial σ E (.ifTrueS e' ee)) $$ Hinv
  | ifFalseS et ee σ =>
      iapply (wp_base_pure trivial σ E (.ifFalseS et e')) $$ Hinv
  | fstS v1 v2 σ =>
      iapply (wp_base_pure trivial σ E (.fstS v1 v2)) $$ Hinv
  | sndS v1 v2 σ =>
      iapply (wp_base_pure trivial σ E (.sndS v1 v2)) $$ Hinv
  | caseLS v et ee σ =>
      iapply (wp_base_pure trivial σ E (.caseLS v et ee)) $$ Hinv
  | caseRS v et ee σ =>
      iapply (wp_base_pure trivial σ E (.caseRS v et ee)) $$ Hinv
  | loadS l v σ hl =>
      iapply (wp_base_atomic_nochange l v σ E
        (base_step_to_val_atomic .StronglyAtomic (.loadS l v σ hl)) hl
        (.loadS l v) loadS_det) $$ Hinv
  | storeS l v w σ hl =>
      iapply (wp_base_atomic l v (some w) σ E
        (base_step_to_val_atomic .StronglyAtomic (.storeS l v w σ hl)) hl
        (.storeS l v w) (fun _ => storeS_det)) $$ Hinv
  | freeS l v σ hl =>
      iapply (wp_base_atomic l v none σ E
        (base_step_to_val_atomic .StronglyAtomic (.freeS l v σ hl)) hl
        (.freeS l v) (fun _ => freeS_det)) $$ Hinv
  | xchgS l v1 v2 σ hl =>
      iapply (wp_base_atomic l v1 (some v2) σ E
        (base_step_to_val_atomic .StronglyAtomic (.xchgS l v1 v2 σ hl)) hl
        (.xchgS l v1 v2) xchgS_det) $$ Hinv
  | faaS l i1 i2 σ hl =>
      iapply (wp_base_atomic l (.lit (.int i1))
        (some (.lit (.int (i1 + i2)))) σ E
        (base_step_to_val_atomic .StronglyAtomic (.faaS l i1 i2 σ hl)) hl
        (.faaS l i1 i2) faaS_det) $$ Hinv
  | cmpXchgS l v1 v2 vl σ b hl hcs hb =>
      cases hb1 : decide (vl = v1) with
      | true =>
          have Hx σ'' h := BaseStep.cmpXchgS l v1 v2 vl σ'' true h hcs (by rw [hb1])
          iapply (wp_base_atomic l vl (some v2) σ E
            (base_step_to_val_atomic .StronglyAtomic (Hx σ hl))
              hl Hx (cmpXchgS_det_true · hb1)) $$ Hinv
      | false =>
          have Hx σ'' h := BaseStep.cmpXchgS l v1 v2 vl σ'' false h hcs (by rw [hb1])
          iapply (wp_base_atomic_nochange l vl σ E
            (base_step_to_val_atomic Atomicity.StronglyAtomic (Hx σ hl))
            hl Hx (cmpXchgS_det_false · hb1)) $$ Hinv
  | forkS e σ =>
      imodintro
      iright
      iframe Hinv
      iintro %Φ %E₂ H
      iapply wp_fork_fupd
      iintro !>
      ihave Htraj : iprop(∀ σ₁, heapInv σ₁ ={E}=∗
          ∃ κ σ₁', ⌜PrimSteps (.fork e) σ₁ κ (.val (.lit .unit)) σ₁' [e]⌝ ∗ heapInv σ₁') $$ []
      · iintro %σ₁ Hheap
        imodintro
        iexists [], σ₁
        iframe Hheap
        ipureintro
        exact .once (EctxLanguage.primStep_of_baseStep (.forkS e σ₁))
      imod H $$ Htraj with ⟨HwpUnit, Hefs⟩
      isplitl [Hefs]
      · iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hefs
      · iapply (wp_value_fupd' (v := .lit .unit)).1 $$ HwpUnit
  | allocNS n v σ l hn hfresh =>
      imodintro
      ileft
      have hatom : Atomic .StronglyAtomic (Exp.allocN (.val (.lit (.int n))) (.val v)) :=
        base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.allocNS n v σ l hn hfresh)
      iframe %hatom
      iintro %Φ Hstep
      iapply wp_lift_atomic_step (EctxLanguage.val_stuck (BaseStep.allocNS n v σ l hn hfresh))
      iintro %σ₁ %ns %obs %obs' %nt Hσ !>
      icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
      obtain ⟨lf, hlf⟩ := exists_fresh_block σ₁.heap n
      have Hred₁ : BaseStep.Reducible (Exp.allocN (.val (.lit (.int n))) (.val v), σ₁) :=
        ⟨[], _, _, [], BaseStep.allocNS n v σ₁ lf hn hlf⟩
      isplit
      · ipureintro
        simp only [Stuckness.MaybeReducible]
        exact EctxLanguage.primStep_reducible_of_baseStep_reducible Hred₁
      iintro !> %e₂ %σ₂ %eₜ %Hprim -
      rcases EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred₁ Hprim
      rename_i l' Hpo Hi
      ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
      icases Hinv with ⟨Hmap, Hproph_inv⟩
      imod (genHeap_alloc_big (allocCells l' n.toNat (some v)) σ₁.heap (allocCells_disjoint Hi))
        $$ Hσ with ⟨Hσ', Hnewpts, Hnewmeta⟩
      ihave %hfreshσ : ⌜∀ i : Int, 0 ≤ i → i < n → get? (M := HeapF) σ.heap (l' + i) = none⌝
          $$ [Hmap Hnewmeta]
      · iintro %i %hi0 %hin
        rcases hgc : get? (M := HeapF) σ.heap (l' + i) with _ | vo
        · itrivial
        · icases (BigSepM.bigSepM_lookup_acc hgc).1 $$ Hmap with ⟨⟨_, Hmeta1⟩, _⟩
          have hcell_new : get? (allocCells l' n.toNat (some v)) (l' + i) = some (some v) := by
            rw [get?_allocCells, if_pos ⟨i.toNat, by omega, by rw [Int.toNat_of_nonneg hi0]⟩]
          icases (BigSepM.bigSepM_lookup_acc hcell_new).1 $$ Hnewmeta with ⟨Hmeta2, _⟩
          icases metaToken_ne CoPset.top_ne_empty $$ Hmeta1 Hmeta2 with %hne
          exact absurd rfl hne
      imod Hstep $$ [] with ⟨Hpost, _⟩
      · ipureintro
        exact EctxLanguage.primStep_of_baseStep (BaseStep.allocNS n v σ l' hn hfreshσ)
      imodintro
      iframe
      isplitl [Hσ' Hproph]
      · simp only [stateInterp]
        iframe
        iapply genHeapInterp_eqv (Std.PartialMap.equiv.symm _ _ initHeap_heap_eq)
        iexact Hσ'
      iexists (.lit (.loc l'))
      isplit; ipureintro; simp [toVal]; rfl
      iapply Hpost
      simp only [heapInv]
      iframe
      iapply (BigSepM.bigSepM_eqv_of_perm initHeap_heap_eq).2
      iapply (BigSepM.bigSepM_union (allocCells_disjoint hfreshσ)).2
      iframe
      iapply BigSepM.bigSepM_sep_eq
      iframe
      iapply (BigSepM.bigSepM_mono_of_forall (fun {k vo} => pointsTo_heapCellPts k vo)) $$ Hnewpts
  | newProphS σ p hp =>
      imodintro
      ileft
      isplit
      · ipureintro
        exact base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.newProphS σ p hp)
      iintro %Φ Hstep
      iapply wp_lift_atomic_step (EctxLanguage.val_stuck (BaseStep.newProphS σ p hp))
      iintro %σ₁ %ns %obs %obs' %nt Hσ !>
      icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
      obtain ⟨pf, Hpf⟩ := Std.List.fresh σ₁.usedProphId.toList
      have Hpf_contains : ¬ σ₁.usedProphId.contains pf := by
        intro hc; exact Hpf (Std.ExtTreeSet.mem_toList.mpr hc)
      have Hred₁ : BaseStep.Reducible (Exp.newProph, σ₁) :=
        ⟨[], _, _, [], BaseStep.newProphS σ₁ pf Hpf_contains⟩
      isplitr
      · ipureintro
        simp only [Stuckness.MaybeReducible]
        exact EctxLanguage.primStep_reducible_of_baseStep_reducible Hred₁
      iintro !> %e₂ %σ₂ %eₜ %Hprim -
      cases EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred₁ Hprim
      rename_i p' Hp'
      ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
      have Hp'_mem : p' ∉ σ₁.usedProphId :=
        fun hmem => Hp' (Std.ExtTreeSet.mem_iff_contains.symm.mp hmem)
      imod (ProphMap.new_proph p' σ₁.usedProphId obs' Hp'_mem) $$ Hproph
        with ⟨Hproph', Htok⟩
      icases Hinv with ⟨Hmap, Hproph_inv⟩
      ihave %Hfresh_σ : ⌜p' ∉ σ.usedProphId⌝ $$ [Hproph_inv Htok]
      · iintro %hmem
        icases BigSepS.bigSepS_elem_of_acc hmem $$ Hproph_inv with ⟨⟨%pvs', Htok'⟩, _⟩
        iapply proph_exclusive $$ Htok Htok'
      have Hfresh_σ_contains : ¬ σ.usedProphId.contains p' := fun hc =>
        Hfresh_σ (Std.ExtTreeSet.mem_iff_contains.symm.mpr hc)
      imod Hstep $$ [] with ⟨Hpost, _⟩
      · ipureintro
        exact EctxLanguage.primStep_of_baseStep (BaseStep.newProphS σ p' Hfresh_σ_contains)
      imodintro
      isplitl [Hσ Hproph']
      · simp only [stateInterp]
        iframe Hσ
        rw [show ({p'} ∪ σ₁.usedProphId : Std.ExtTreeSet ProphId compare)
            = σ₁.usedProphId.insert p' from insert_eq_singleton_union_extTreeSet.symm]
        iexact Hproph'
      iframe
      iexists (.lit (.prophecy p'))
      isplit; ipureintro; simp [toVal]; rfl
      iapply Hpost
      simp only [heapInv]
      iframe
      rw [insert_eq_singleton_union_extTreeSet (ps := σ.usedProphId) (p := p')]
      have hdisj : ({p'} : Std.ExtTreeSet ProphId compare) ## σ.usedProphId := by
        intro x ⟨h1, h2⟩
        rw [Std.LawfulSet.mem_singleton] at h1
        subst h1
        exact Hfresh_σ h2
      iapply (BigSepS.bigSepS_union hdisj).mpr
      iframe
      iapply BigSepS.bigSepS_singleton.mpr
      iexists (prophListResolves obs' p')
      iexact Htok
  | resolveS p v e σ w σ' κs ts hbase hp =>
      have IH : heapInv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e σ E) :=
        wp_baseCompletenessGoal e σ E ⟨κs, _, _, _, hbase⟩
      have hatom : Atomic Atomicity.StronglyAtomic
          (Exp.resolve e (.val (.lit (.prophecy p))) (.val w)) :=
        base_step_to_val_atomic Atomicity.StronglyAtomic
          (BaseStep.resolveS p v e σ w σ' κs efs hbase hp)
      have hatom_e : Atomic Atomicity.StronglyAtomic e :=
        base_step_to_val_atomic Atomicity.StronglyAtomic hbase
      have hne_e : toVal e = none := EctxLanguage.val_stuck hbase
      have hp_mem : p ∈ σ.usedProphId := Std.ExtTreeSet.mem_iff_contains.symm.mpr hp
      imodintro
      ileft
      iframe %hatom; clear hatom
      iintro %Φ Hstep
      icases Hinv with ⟨Hmap, Hproph_inv⟩
      icases BigSepS.bigSepS_elem_of_acc hp_mem $$ Hproph_inv with ⟨⟨%pvs, Htok⟩, HcloseProph⟩
      iapply (wp_resolve_strong hatom_e hne_e) $$ Htok
      iintro Hele
      ihave Hinv_full : heapInv σ $$ [Hmap HcloseProph Hele]
      · unfold heapInv
        iframe
        iapply HcloseProph
        iexists pvs; iexact Hele
      ihave Hinner : iprop(|={E}=> baseCompletenessGoal e σ E) $$ [Hinv_full]
      · iapply IH $$ [$]
      iapply fupd_wp
      imod Hinner with H
      imodintro
      icases H with (⟨-, Hrst⟩ | ⟨Hinv_back, Hrst_nonatom⟩)
      · iapply Hrst
        iintro !> %κ_e %v_e %σ_e %efs_e %Hprim_e
        have Hbase_e : BaseStep e σ κ_e (.val v_e) σ_e efs_e := primStep_val_baseStep Hprim_e
        imod Hstep $$ %_ %_ %_ %_ %(prim_step_resolve_of_inner (w := w) Hbase_e hp)
          with ⟨Hwp_outer, Hefs⟩
        imodintro
        iframe Hefs
        iintro ⟨Hmap_e, Hproph_inv_e⟩
        have hp_mem_e : p ∈ σ_e.usedProphId := base_step_more_proph_ids Hbase_e p hp_mem
        icases BigSepS.bigSepS_elem_of_acc hp_mem_e $$ Hproph_inv_e
          with ⟨⟨%pvs2, Hele2⟩, HcloseProph_e⟩
        iexists pvs2
        iframe Hele2
        iintro %pvs'' %heq Hele2'
        subst heq
        iapply Hwp_outer
        unfold heapInv
        iframe Hmap_e
        iapply HcloseProph_e
        iexists pvs''; iexact Hele2'
      · iapply Hrst_nonatom
        iintro !> %e₂_e %efs_e Htraj_e
        imod Htraj_e $$ %_ Hinv_back with ⟨%κ_e, %σ_e, %Hprims, ⟨Hmap_e, Hproph_inv_e⟩⟩
        obtain ⟨Hprim_e, hval_e⟩ := primSteps_atomic (e := e) hatom_e Hprims
        obtain ⟨v_e, rfl⟩ : ∃ v_e, e₂_e = Exp.val v_e := by
          match e₂_e, hval_e with | .val v_e, _ => exact ⟨v_e, rfl⟩
        have Hbase_e : BaseStep e σ κ_e (.val v_e) σ_e efs_e := primStep_val_baseStep Hprim_e
        imod Hstep $$ %_ %_ %_ %_ %(prim_step_resolve_of_inner (w := w) Hbase_e hp)
          with ⟨Hwp_outer, Hefs⟩
        imodintro
        have hp_mem_e : p ∈ σ_e.usedProphId := base_step_more_proph_ids Hbase_e p hp_mem
        icases BigSepS.bigSepS_elem_of_acc hp_mem_e $$ Hproph_inv_e
          with ⟨⟨%pvs2, Hele2⟩, HcloseProph_e⟩
        iframe
        iapply wp_value'
        iexists pvs2
        iframe Hele2
        iintro %pvs'' %heq Hele2'
        subst heq
        iapply Hwp_outer
        unfold heapInv
        iframe Hmap_e
        iapply HcloseProph_e
        iexists pvs''
        iexact Hele2'
termination_by e₁

section Framework

variable {H : Type _ → Type _} [LawfulFiniteMap H Nat] [TpinvGS GF Exp H]

theorem wp_base_completeness {n C e₁ σ K E} :
  ⊢@{IProp GF} ectxLangCompletenessStmt (Wp.wp Stuckness.NotStuck)
        (fun (_ : List Exp) (σ : State) => heapInv σ) n C e₁ σ K E := by
  unfold ectxLangCompletenessStmt
  iintro %Hred Htok ⟨Hheap, Htp, %_Hsafe⟩
  imod (wp_baseCompletenessGoal e₁ σ E Hred) $$ Hheap with (⟨%Hatom, H⟩ | ⟨Hheap, H⟩)
  · -- Atomic redex.
    imodintro
    ileft
    have Hwa : Atomic Atomicity.WeaklyAtomic e₁ := stronglyAtomic_atomic Hatom
    iframe %Hwa
    iintro %Φ Hx
    iapply H
    iintro !> %κ %v₂ %σ' %efs %Hprim
    iapply Hx $$ [] Htok Htp
    ipureintro; exact Hprim
  · -- Non-atomic redex.
    imodintro
    iright
    iframe Hheap Htp
    iintro %Φ Hx
    iapply H
    iintro !> %e₂ %efs HH
    iapply Hx
    iintro %σ₁ %C₁ ⟨Hsi, Htp, %_Hs⟩
    imod HH $$ Hsi with ⟨%κ, %σ₁', %Hprims, Hhp⟩
    imodintro
    iexists κ, σ₁'
    iframe Htok Htp Hhp
    ipureintro
    exact Hprims

instance heap_lang_completeness :
    AbstractEctxLangCompletenessGen (Expr := Exp) (Ectx := List ECtxItem)
      (Wp.wp (PROP := IProp GF) Stuckness.NotStuck) where
  heap_inv _ := heapInv
  heap_inv_timeless _ := instTimeless_heapInv
  ectx_lang_completeness _ _ _ _ _ _ := wp_base_completeness

end Framework

section Endpoint

variable {H : Type _ → Type _} [LawfulFiniteMap H Nat] [GhostMapG GF Nat Exp H] [CInvG GF]
include H

theorem heap_lang_sem_completeness (e : Exp) (σ : State) (φ : Val → Prop)
    (Hade : adequate Stuckness.NotStuck e σ (fun v _ => φ v)) :
    ⊢ heapInv (GF := GF) σ -∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} := by
  iintro Hheap
  imod (tpInv_alloc (GF := GF) (Expr := Exp) (H := H)) with ⟨%γ, Hini⟩
  letI TI : TpinvGS GF Exp H := { toGhostMapG := inferInstance, tp_name := γ }
  ihave Hwp := weakestpre_sem_completeness
    (wp := Wp.wp (PROP := IProp GF) Stuckness.NotStuck) e σ φ Hade $$ Hini Hheap
  iexact Hwp

theorem heap_lang_sem_completeness_nofork (e : Exp) (σ : State) (φ : Val → State → Prop)
    (Hade : AdequateNoFork Stuckness.NotStuck e σ (fun v σ' => φ v σ')) :
    ⊢ heapInv (GF := GF) σ -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ∃ σ' : State, heapInv σ' ∗ ⌜φ v σ'⌝ }} := by
  iintro Hheap
  imod (tpInv_alloc (GF := GF) (Expr := Exp) (H := H)) with ⟨%γ, Hini⟩
  letI TI : TpinvGS GF Exp H := { toGhostMapG := inferInstance, tp_name := γ }
  ihave Hwp := weakestpre_sem_completeness_nofork
    (wp := Wp.wp (PROP := IProp GF) Stuckness.NotStuck) e σ φ Hade $$ Hini Hheap
  iexact Hwp

end Endpoint

end Iris.HeapLang
