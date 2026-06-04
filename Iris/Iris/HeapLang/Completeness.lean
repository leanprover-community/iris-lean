/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.HeapLang.PrimitiveLaws
public import Iris.ProgramLogic.ThreadPool
public import Iris.ProgramLogic.AbstractWeakestPre
public import Iris.ProgramLogic.AbstractLangCompleteness
public import Iris.ProgramLogic.AbstractEctxLangCompleteness
public import Iris.Instances.Lib.CInvariants
public import Iris.Instances.Lib.GhostMap
public import Iris.ProofMode

/-! # HeapLang completeness

Ports `case_studies/heaplang/completeness_generic.v` and
`completeness_classical.v`, dropping the prophecy machinery and (for now) the
`meta_token` conjunct of `heap_inv` (not yet implemented upstream in
`BI/Lib/GenHeap.lean`).

Status of `wp_base_completeness` (the base-step case analysis):
* pure branches (`rec`/`pair`/`injL`/`injR`/`beta`/`unop`/`binop`/`if`/`fst`/
  `snd`/`case`) — complete, via `wp_base_pure` + the `PureExec` instances;
* atomic heap branches (`load`/`store`/`free`/`xchg`/`faa`) — reduced via
  `wp_base_atomic`(`_nochange`) to a small per-op determinism fact, `sorry`'d;
* `cmpXchg` and `fork` — not yet wired (`sorry`);
* `alloc` — needs `meta_token_ne` for location freshness (`sorry`);
* `newProph`/`resolve` — dropped (prophecy out of scope, `sorry`).
-/

@[expose] public section
namespace Iris.HeapLang

open Iris ProgramLogic Iris.BI Language Language.Notation Std

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF]

/-- The heap-lang configuration invariant: ownership of every heap cell. The
`meta_token` conjunct of the Rocq `heap_inv` is dropped (not yet available), as
is the prophecy conjunct (out of scope). Mirrors `heap_inv` in
`case_studies/heaplang/completeness_generic.v`. -/
@[reducible] def heap_inv (σ : State) : IProp GF :=
  bigSepM (M := HeapF) (K := Loc) (fun (l : Loc) (vo : Option Val) => iprop(l ↦ vo)) σ.heap

instance heap_inv_timeless (σ : State) : Timeless (heap_inv (GF := GF) σ) := by
  unfold heap_inv; infer_instance

/-- Common shape of the completeness equation for a single base step, packaged so
the per-branch proofs only have to supply the (atomic / non-atomic) disjunct. -/
abbrev baseCompletenessGoal (e₁ : Exp) (σ : State) (E : CoPset) : IProp GF := iprop(
    ((⌜Atomic Atomicity.StronglyAtomic e₁⌝ ∗
        ∀ (Φ : Val → IProp GF),
          (▷ ∀ κ v₂ σ' efs, ⌜PrimStep.primStep (e₁, σ) κ ((ToVal.ofVal v₂ : Exp), σ', efs)⌝ ==∗
            ((heap_inv σ' -∗ Φ v₂) ∗
              [∗list] _i ↦ etp ∈ efs, WP etp @ Stuckness.NotStuck; ⊤ {{ _v, True }})) -∗
          WP e₁ @ Stuckness.NotStuck; E {{ v, Φ v }}) ∨
     (heap_inv σ ∗
        ∀ (Φ : Val → IProp GF) (E₂ : CoPset),
          (▷ ∀ e₂ efs, (∀ σ₁, heap_inv σ₁ ={E}=∗
              ∃ κ σ₁', ⌜PrimSteps e₁ σ₁ κ e₂ σ₁' efs⌝ ∗ heap_inv σ₁') ={E₂}=∗
            WP e₂ @ Stuckness.NotStuck; E₂ {{ v, Φ v }} ∗
            [∗list] _i ↦ etp ∈ efs, WP etp @ Stuckness.NotStuck; ⊤ {{ _v, True }}) -∗
          WP e₁ @ Stuckness.NotStuck; E₂ {{ v, Φ v }})))

/-- Pure-step branch of `wp_base_completeness`: a pure base step `e₁ → e₂` lands in
the non-atomic disjunct, stepping the WP with `PureExec` and witnessing the
trajectory with the (state-independent) base step. -/
theorem wp_base_pure {e₁ e₂ : Exp} {φ : Prop} (hpe : Language.PureExec φ 1 e₁ e₂) (hφ : φ)
    (σ : State) (E : CoPset)
    (hbase : ∀ σ' : State, BaseStep e₁ σ' [] e₂ σ' []) :
    heap_inv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro Hinv
  unfold baseCompletenessGoal
  imodintro
  iright
  iframe Hinv
  iintro %Φ %E₂ H
  iapply wp_pure_step_later (Hexec := hpe) (Hφ := hφ)
  iintro !> _
  ihave Htraj : iprop(∀ σ₁, heap_inv σ₁ ={E}=∗
      ∃ κ σ₁', ⌜PrimSteps e₁ σ₁ κ e₂ σ₁' []⌝ ∗ heap_inv σ₁') $$ []
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

/-- Atomic heap-step branch of `wp_base_completeness`: a deterministic heap
operation at location `l` (reading cell `vold`, writing `vnew`, returning `v₂`)
lands in the atomic disjunct. The WP's own step (via `wp_lift_atomic_step`)
exposes the later needed to strip the magic premise. -/
theorem wp_base_atomic {e₁ : Exp} {v₂ : Val} (l : Loc) (vold vnew : Option Val)
    (σ : State) (E : CoPset)
    (hatom : Atomic Atomicity.StronglyAtomic e₁)
    (hcell : get? (M := HeapF) σ.heap l = some vold)
    (hbase : ∀ σ'' : State, get? (M := HeapF) σ''.heap l = some vold →
        BaseStep e₁ σ'' [] (ToVal.ofVal v₂) (σ''.initHeap l 1 vnew) [])
    (hdet : ∀ {σ'' : State} {obs e' σ''' efs}, get? (M := HeapF) σ''.heap l = some vold →
        BaseStep e₁ σ'' obs e' σ''' efs →
        obs = [] ∧ e' = (ToVal.ofVal v₂ : Exp) ∧ σ''' = σ''.initHeap l 1 vnew ∧ efs = []) :
    heap_inv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro Hinv
  unfold baseCompletenessGoal
  imodintro
  ileft
  iframe %hatom
  iintro %Φ Hstep
  icases (BigSepM.bigSepM_insert_acc (M := HeapF)
    (Φ := fun (k : Loc) (vo : Option Val) => iprop(k ↦ vo)) hcell) $$ Hinv with ⟨Hpt, Hclose⟩
  iapply wp_lift_atomic_step (EctxLanguage.val_stuck (hbase σ hcell))
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %hcell1 : ⌜get? (M := HeapF) σ₁.heap l = some vold⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%hh
    itrivial
  isplitr
  · ipureintro
    simp only [Stuckness.MaybeReducible]
    exact EctxLanguage.primStep_reducible_of_baseStep_reducible
      ⟨[], _, _, [], hbase σ₁ hcell1⟩
  iintro !> %e₂ %σ₂ %eₜ %Hprim Hcr
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    hdet hcell1 (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible ⟨[], _, _, [], hbase σ₁ hcell1⟩ Hprim)
  imod genHeap_update (v₂ := vnew) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hstep $$ [] with ⟨Hpost, _⟩
  · ipureintro
    exact EctxLanguage.primStep_of_baseStep (hbase σ hcell)
  imodintro
  have hl0 : l + (0 : Int) = l := by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind
  simp only [stateInterp, State.initHeap, Int.toNat_one, List.range_one, List.foldl_cons,
    Int.cast_ofNat_Int, List.foldl_nil, hl0, List.length_nil, Nat.add_zero,
    Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  isplitl [Hpost Hclose Hpt]
  · iexists v₂
    isplit
    · ipureintro; simp [toVal]
    iapply Hpost
    simp only [heap_inv, State.initHeap, Int.toNat_one, List.range_one, List.foldl_cons,
      Int.cast_ofNat_Int, List.foldl_nil, hl0]
    iapply Hclose $$ Hpt
  · itrivial

/-- Atomic heap-step branch that leaves the heap unchanged (read-only ops: `load`,
failing `cmpXchg`). -/
theorem wp_base_atomic_nochange {e₁ : Exp} {v₂ : Val} (l : Loc) (vcur : Option Val)
    (σ : State) (E : CoPset)
    (hatom : Atomic Atomicity.StronglyAtomic e₁)
    (hcell : get? (M := HeapF) σ.heap l = some vcur)
    (hbase : ∀ σ'' : State, get? (M := HeapF) σ''.heap l = some vcur →
        BaseStep e₁ σ'' [] (ToVal.ofVal v₂) σ'' [])
    (hdet : ∀ {σ'' : State} {obs e' σ''' efs}, get? (M := HeapF) σ''.heap l = some vcur →
        BaseStep e₁ σ'' obs e' σ''' efs →
        obs = [] ∧ e' = (ToVal.ofVal v₂ : Exp) ∧ σ''' = σ'' ∧ efs = []) :
    heap_inv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro Hinv
  unfold baseCompletenessGoal
  imodintro
  ileft
  iframe %hatom
  iintro %Φ Hstep
  iapply wp_lift_atomic_step (EctxLanguage.val_stuck (hbase σ hcell))
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  simp only [stateInterp]
  ihave %hcell1 : ⌜get? (M := HeapF) σ₁.heap l = some vcur⌝ $$ [Hσ Hinv]
  · icases (BigSepM.bigSepM_lookup_acc (M := HeapF)
      (Φ := fun (k : Loc) (vo : Option Val) => iprop(k ↦ vo)) hcell).1 $$ Hinv with ⟨Hpt, _⟩
    icases genHeap_valid $$ [$Hσ $Hpt] with >%hh
    itrivial
  isplitr
  · ipureintro
    simp only [Stuckness.MaybeReducible]
    exact EctxLanguage.primStep_reducible_of_baseStep_reducible
      ⟨[], _, _, [], hbase σ₁ hcell1⟩
  iintro !> %e₂ %σ₂ %eₜ %Hprim Hcr
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    hdet hcell1 (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible
      ⟨[], _, _, [], hbase σ₁ hcell1⟩ Hprim)
  imod Hstep $$ [] with ⟨Hpost, _⟩
  · ipureintro
    exact EctxLanguage.primStep_of_baseStep (hbase σ hcell)
  imodintro
  iframe Hσ
  isplitl [Hpost Hinv]
  · iexists v₂
    isplit
    · ipureintro; simp [toVal]
    iapply Hpost
    iexact Hinv
  · itrivial

/-- The heap-only completeness equation: case analysis on the base step. Mirrors
`wp_base_completeness` in `case_studies/heaplang/completeness_generic.v`.

See the module header for the per-branch status; the remaining `sorry`s are the
per-op determinism facts for the heap branches, `cmpXchg`/`fork`, the `alloc`
freshness argument (`meta_token`), and the dropped prophecy branches. -/
theorem wp_base_completeness (e₁ : Exp) (σ : State) (E : CoPset)
    (Hred : BaseStep.Reducible (e₁, σ)) :
    heap_inv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro Hinv
  obtain ⟨κ, e', σ', efs, Hstep⟩ := Hred
  cases Hstep with
  | recS f x e σ =>
      iapply (wp_base_pure PureExec_rec trivial σ E (fun σ' => BaseStep.recS f x e σ')) $$ Hinv
  | pairS v1 v2 σ =>
      iapply (wp_base_pure PureExec_pair trivial σ E (fun σ' => BaseStep.pairS v1 v2 σ')) $$ Hinv
  | injLS v σ =>
      iapply (wp_base_pure PureExec_injL trivial σ E (fun σ' => BaseStep.injLS v σ')) $$ Hinv
  | injRS v σ =>
      iapply (wp_base_pure PureExec_injR trivial σ E (fun σ' => BaseStep.injRS v σ')) $$ Hinv
  | betaS f x eb v2 e' σ h =>
      subst h
      iapply (wp_base_pure instPureExecBeta trivial σ E
        (fun σ' => BaseStep.betaS f x eb v2 _ σ' rfl)) $$ Hinv
  | unOpS op v v' σ h =>
      iapply (wp_base_pure (PureExec_unop (op := op) (v := v) (v' := v')) h σ E
        (fun σ' => BaseStep.unOpS op v v' σ' h)) $$ Hinv
  | binOpS op v1 v2 v' σ h =>
      iapply (wp_base_pure (PureExec_binop (op := op) (v1 := v1) (v2 := v2) (v' := v')) h σ E
        (fun σ' => BaseStep.binOpS op v1 v2 v' σ' h)) $$ Hinv
  | ifTrueS et ee σ =>
      iapply (wp_base_pure instPureExecIfTrue trivial σ E (fun σ' => BaseStep.ifTrueS e' ee σ')) $$ Hinv
  | ifFalseS et ee σ =>
      iapply (wp_base_pure instPureExecIfFalse trivial σ E (fun σ' => BaseStep.ifFalseS et e' σ')) $$ Hinv
  | fstS v1 v2 σ =>
      iapply (wp_base_pure PureExec_fst trivial σ E (fun σ' => BaseStep.fstS v1 v2 σ')) $$ Hinv
  | sndS v1 v2 σ =>
      iapply (wp_base_pure PureExec_snd trivial σ E (fun σ' => BaseStep.sndS v1 v2 σ')) $$ Hinv
  | caseLS v et ee σ =>
      iapply (wp_base_pure PureExec_caseL trivial σ E (fun σ' => BaseStep.caseLS v et ee σ')) $$ Hinv
  | caseRS v et ee σ =>
      iapply (wp_base_pure PureExec_caseR trivial σ E (fun σ' => BaseStep.caseRS v et ee σ')) $$ Hinv
  | loadS l v σ hl =>
      iapply (wp_base_atomic_nochange (v₂ := v) l (some v) σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.loadS l v σ hl)) hl
        (fun σ'' h => BaseStep.loadS l v σ'' h)
        (fun {σ''} h hs => by sorry)) $$ Hinv
  | storeS l v w σ hl =>
      iapply (wp_base_atomic (v₂ := .lit .unit) l (some v) (some w) σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.storeS l v w σ hl)) hl
        (fun σ'' h => BaseStep.storeS l v w σ'' h)
        (fun {σ''} h hs => by sorry)) $$ Hinv
  | freeS l v σ hl =>
      iapply (wp_base_atomic (v₂ := .lit .unit) l (some v) none σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.freeS l v σ hl)) hl
        (fun σ'' h => BaseStep.freeS l v σ'' h)
        (fun {σ''} h hs => by sorry)) $$ Hinv
  | xchgS l v1 v2 σ hl =>
      iapply (wp_base_atomic (v₂ := v1) l (some v1) (some v2) σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.xchgS l v1 v2 σ hl)) hl
        (fun σ'' h => BaseStep.xchgS l v1 v2 σ'' h)
        (fun {σ''} h hs => by sorry)) $$ Hinv
  | faaS l i1 i2 σ hl =>
      iapply (wp_base_atomic (v₂ := .lit (.int i1)) l (some (.lit (.int i1)))
        (some (.lit (.int (i1 + i2)))) σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.faaS l i1 i2 σ hl)) hl
        (fun σ'' h => BaseStep.faaS l i1 i2 σ'' h)
        (fun {σ''} h hs => by sorry)) $$ Hinv
  | cmpXchgS l v1 v2 vl σ b hl hcs hb => sorry
  | forkS e σ => sorry
  | allocNS n v σ l hn hfresh => sorry
  | newProphS σ p hp => sorry
  | resolveS p v e σ w σ' κs ts hbase hp => sorry

section Framework

variable {H : Type _ → Type _} [LawfulFiniteMap H Nat] [TI : TpinvGS GF Exp H]

/-- The framework-facing heap-lang completeness equation: the `ectx`-level
soundness equation specialized to heap_lang's `heap_inv`. Mirrors
`wp_base_completeness_actual` in `case_studies/heaplang/completeness_generic.v`. -/
theorem wp_base_completeness_actual
    (n : Nat) (C : List Exp) (e₁ : Exp) (σ : State) (K : List ECtxItem) (E : CoPset) :
    ⊢ ectxLangCompletenessStmt (Wp.wp (PROP := IProp GF) Stuckness.NotStuck)
        (fun (_ : List Exp) (σ : State) => heap_inv σ) n C e₁ σ K E := by
  unfold ectxLangCompletenessStmt
  iintro %Hred Htok ⟨Hheap, Htp, %Hsafe⟩
  imod (wp_base_completeness e₁ σ E Hred) $$ Hheap with (⟨%Hatom, H⟩ | ⟨Hheap, H⟩)
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

/-- HeapLang is an instance of the abstract ectx-completeness theory. Mirrors
`heap_lang_completeness` in `case_studies/heaplang/completeness_generic.v`. -/
instance heap_lang_completeness :
    AbstractEctxLangCompletenessGen (Expr := Exp) (Ectx := List ECtxItem)
      (Wp.wp (PROP := IProp GF) Stuckness.NotStuck) where
  heap_inv _C σ := heap_inv σ
  heap_inv_timeless C σ := heap_inv_timeless σ
  ectx_lang_completeness n C e₁ σ K E := wp_base_completeness_actual n C e₁ σ K E

end Framework

section Endpoint

/-- **Top-level heap-lang completeness**: an adequate program admits a WP with the
adequacy postcondition. Mirrors `heap_lang_sem_completeness` in
`case_studies/heaplang/completeness_classical.v`. -/
theorem heap_lang_sem_completeness {H : Type _ → Type _} [LawfulFiniteMap H Nat]
    [GhostMapG GF Qp Nat Exp H] [CInvG Qp GF]
    (e : Exp) (σ : State) (φ : Val → Prop)
    (Hade : adequate Stuckness.NotStuck e σ (fun v _ => φ v)) :
    ⊢ heap_inv (GF := GF) σ -∗ WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} := by
  iintro Hheap
  imod (tpInv_alloc (GF := GF) (Expr := Exp) (H := H)) with ⟨%γ, Hini⟩
  letI TI : TpinvGS GF Exp H := { toGhostMapG := inferInstance, tp_name := γ }
  ihave Hwp := weakestpre_sem_completeness
    (wp := Wp.wp (PROP := IProp GF) Stuckness.NotStuck) e σ φ Hade $$ Hini Hheap
  iexact Hwp

/-- Nofork variant. Mirrors `heap_lang_sem_completeness_nofork`. -/
theorem heap_lang_sem_completeness_nofork {H : Type _ → Type _} [LawfulFiniteMap H Nat]
    [GhostMapG GF Qp Nat Exp H] [CInvG Qp GF]
    (e : Exp) (σ : State) (φ : Val → State → Prop)
    (Hade : AdequateNoFork Stuckness.NotStuck e σ (fun v σ' => φ v σ')) :
    ⊢ heap_inv (GF := GF) σ -∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ∃ σ' : State, heap_inv σ' ∗ ⌜φ v σ'⌝ }} := by
  iintro Hheap
  imod (tpInv_alloc (GF := GF) (Expr := Exp) (H := H)) with ⟨%γ, Hini⟩
  letI TI : TpinvGS GF Exp H := { toGhostMapG := inferInstance, tp_name := γ }
  ihave Hwp := weakestpre_sem_completeness_nofork
    (wp := Wp.wp (PROP := IProp GF) Stuckness.NotStuck) e σ φ Hade $$ Hini Hheap
  iexact Hwp

end Endpoint

end Iris.HeapLang
