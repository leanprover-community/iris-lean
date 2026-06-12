/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

Ports `case_studies/heaplang/completeness_generic.v` and
`completeness_classical.v`. `heap_inv` carries Rocq's two conjuncts: per-cell
`heapCellPts ∗ meta_token` (mirroring `from_option (λ v, ℓ ↦ v) ⌜True⌝` — a live
cell owns its points-to, a freed `none` cell owns nothing), and
`∃ pvs, proph p pvs` for every prophecy id in `σ.usedProphId`. `stateInterp`
includes `prophMapInterp κs σ.usedProphId` alongside `genHeapInterp σ.heap`.

Status of `wp_base_completeness` (the base-step case analysis):
* pure branches (`rec`/`pair`/`injL`/`injR`/`beta`/`unop`/`binop`/`if`/`fst`/
  `snd`/`case`) — via `wp_base_pure` + the `PureExec` instances/lemmas;
* atomic heap branches (`load`/`store`/`free`/`xchg`/`faa`/`cmpXchg`) — via
  `wp_base_atomic`(`_nochange`) + the per-op determinism lemmas;
* `fork` — via the non-atomic disjunct and `wp_fork_fupd`;
* `alloc` — via `genHeap_alloc_big`, with location freshness from `meta_token_ne`;
* `newProph` — atomic lift, fresh `p` picked in `σ₁.usedProphId`, then
  `ProphMap.new_proph` allocates a proph token; freshness in `σ` follows from
  `proph_exclusive` against the proph conjunct of `heap_inv σ`;
* `resolve` — `sorry` body, but `wp_base_completeness` is now a well-founded
  recursion on `e₁` (declared via `termination_by e₁`), so the resolveS branch
  has the inductive hypothesis `IH : heap_inv σ ⊢ |={E}=> baseCompletenessGoal
  e σ E` in scope for the inner expression `e`. What remains is the body that
  combines `IH` with the outer Resolve wrapping (mirror of Rocq lines 127–159):
  extract `proph p` from `heap_inv σ`'s proph conjunct via `bigSepS_elem_of_acc`
  + `hp : p ∈ σ.usedProphId`, then either inline a `wp_resolve_strong`-style
  argument or split on `IH`'s atomic/non-atomic disjunction and use
  `ProphMap.resolve_proph` to consume the front observation `(p,(v,w))` of
  `κs`. All other supporting infrastructure (`prophMapInterp`, `proph p pvs`,
  `ProphMap.resolve_proph`, the proph conjunct of `heap_inv`, the recursion)
  is in place.
-/

@[expose] public section
namespace Iris.HeapLang

open Iris ProgramLogic Iris.BI Language Language.Notation Std

variable {hlc : HasLC} {GF : BundledGFunctors} [HeapLangGS hlc GF]

/-- Ownership of a single heap cell's points-to. Mirrors Rocq's
`from_option (λ v, ℓ ↦ v) ⌜True⌝`: a live cell `some v` contributes `l ↦ some v`,
while a freed cell `none` contributes no ownership (`emp`). Note iris-lean's
`l ↦ ·` is the raw `gen_heap` points-to over `Option Val`, unlike Rocq heap_lang's
sealed `↦` which always wraps `Some`; hence the explicit `match` here. -/
@[reducible] def heapCellPts (l : Loc) (vo : Option Val) : IProp GF :=
  match vo with
  | some _ => iprop(l ↦ vo)
  | none => iprop(emp)

instance heapCellPts_timeless (l : Loc) (vo : Option Val) :
    Timeless (heapCellPts (GF := GF) l vo) := by
  cases vo <;> (unfold heapCellPts; infer_instance)

/-- The raw points-to entails the cell invariant: for a live cell it is the same
resource, for a freed cell the points-to is dropped (affinely). -/
theorem pointsTo_heapCellPts (l : Loc) (vo : Option Val) :
    (l ↦ vo) ⊢ heapCellPts (GF := GF) l vo := by
  cases vo with
  | some v => exact .rfl
  | none => exact BI.Affine.affine

/-- The heap-lang configuration invariant: ownership of every live heap cell's
points-to together with the `meta_token` of every cell (live or freed), and a
`proph` token for every used prophecy id.
Mirrors `heap_inv` in `case_studies/heaplang/completeness_generic.v`. -/
@[reducible] def heap_inv (σ : State) : IProp GF := iprop(
    (bigSepM (M := HeapF) (K := Loc)
       (fun (l : Loc) (vo : Option Val) => iprop(heapCellPts l vo ∗ metaToken l ⊤)) σ.heap) ∗
    ([∗set] p ∈ σ.usedProphId, ∃ pvs : List (Val × Val), proph p pvs))

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
operation at a live location `l` (reading cell `some vlive`, writing `vnew`,
returning `v₂`) lands in the atomic disjunct. The WP's own step (via
`wp_lift_atomic_step`) exposes the later needed to strip the magic premise. -/
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
    heap_inv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro ⟨Hmap, Hproph_inv⟩
  unfold baseCompletenessGoal
  imodintro
  ileft
  iframe %hatom
  iintro %Φ Hstep
  -- For the live cell, `heapCellPts l (some vlive)` reduces to `l ↦ some vlive`.
  icases (BigSepM.bigSepM_insert_acc (M := HeapF)
    (Φ := fun (k : Loc) (vo : Option Val) => iprop(heapCellPts k vo ∗ metaToken k ⊤)) hcell)
    $$ Hmap with ⟨⟨Hpt, Hmeta⟩, Hclose⟩
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
  iintro !> %e₂ %σ₂ %eₜ %Hprim Hcr
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    hdet hcell1 (EctxLanguage.baseStep_of_primStep_of_baseStep_reducible ⟨[], _, _, [], hbase σ₁ hcell1⟩ Hprim)
  imod genHeap_update (v₂ := vnew) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hstep $$ [] with ⟨Hpost, _⟩
  · ipureintro
    exact EctxLanguage.primStep_of_baseStep (hbase σ hcell)
  imodintro
  ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
  have hl0 : l + (0 : Int) = l := by cases l; simp only [HAdd.hAdd, Loc.mk.injEq]; grind
  simp only [stateInterp, State.initHeap, Int.toNat_one, List.range_one, List.foldl_cons,
    Int.cast_ofNat_Int, List.foldl_nil, hl0,
    Algebra.BigOpL.bigOpL_nil]
  iframe Hσ Hproph
  isplitl [Hpost Hclose Hpt Hmeta Hproph_inv]
  · iexists v₂
    isplit
    · ipureintro; simp [toVal]
    iapply Hpost
    simp only [heap_inv]
    isplitl [Hclose Hpt Hmeta]
    · iapply Hclose
      isplitl [Hpt]
      -- Convert the raw points-to back into the cell invariant (`emp` if freed).
      · iapply (pointsTo_heapCellPts l vnew); iexact Hpt
      · iexact Hmeta
    · iexact Hproph_inv
  · itrivial

/-- Atomic heap-step branch that leaves the heap unchanged (read-only ops: `load`,
failing `cmpXchg`). -/
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
    heap_inv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro ⟨Hmap, Hproph_inv⟩
  unfold baseCompletenessGoal
  imodintro
  ileft
  iframe %hatom
  iintro %Φ Hstep
  iapply wp_lift_atomic_step (EctxLanguage.val_stuck (hbase σ hcell))
  iintro %σ₁ %ns %obs %obs' %nt Hσ !>
  icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
  ihave %hcell1 : ⌜get? (M := HeapF) σ₁.heap l = some (some vlive)⌝ $$ [Hσ Hmap]
  · icases (BigSepM.bigSepM_lookup_acc (M := HeapF)
      (Φ := fun (k : Loc) (vo : Option Val) => iprop(heapCellPts k vo ∗ metaToken k ⊤)) hcell).1
      $$ Hmap with ⟨⟨Hpt, _⟩, _⟩
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
  ihave Hproph := (prophMapInterp_nil_append obs' σ₂.usedProphId).mp $$ Hproph
  simp only [stateInterp]
  iframe Hσ Hproph
  isplitl [Hpost Hmap Hproph_inv]
  · iexists v₂
    isplit
    · ipureintro; simp [toVal]
    iapply Hpost
    simp only [heap_inv]
    iframe Hmap Hproph_inv
  · itrivial

/-! ### Per-operation determinism facts.

These discharge the `hdet` argument of `wp_base_atomic`(`_nochange`): for a fixed
redex and a fixed value of the cell being acted on, the base step's output is
uniquely determined. In Rocq these are obtained for free by reasoning forward
with the concrete `wp_load`/`wp_store`/… rules; here the generic atomic helper
takes the determinism as an explicit side condition. Each is a one-constructor
`cases` followed by reading off the cell equation. -/

theorem loadS_det {l : Loc} {v : Val} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some v))
    (hs : BaseStep (.load (.val (.lit (.loc l)))) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal v : Exp) ∧ σ' = σ ∧ efs = [] := by
  cases hs with
  | loadS _ v' _ h' =>
    simp only [State.get?] at h'
    rw [h] at h'
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h'
    subst h'
    refine ⟨rfl, rfl, rfl, rfl⟩

theorem storeS_det {l : Loc} {w : Val} {σ : State} {obs e' σ' efs}
    (hs : BaseStep (.store (.val (.lit (.loc l))) (.val w)) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.lit .unit) : Exp) ∧
      σ' = σ.initHeap l 1 (some w) ∧ efs = [] := by
  cases hs with
  | storeS _ _ _ _ _ => refine ⟨rfl, rfl, rfl, rfl⟩

theorem freeS_det {l : Loc} {σ : State} {obs e' σ' efs}
    (hs : BaseStep (.free (.val (.lit (.loc l)))) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.lit .unit) : Exp) ∧
      σ' = σ.initHeap l 1 none ∧ efs = [] := by
  cases hs with
  | freeS _ _ _ _ => refine ⟨rfl, rfl, rfl, rfl⟩

theorem xchgS_det {l : Loc} {v1 v2 : Val} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some v1))
    (hs : BaseStep (.xchg (.val (.lit (.loc l))) (.val v2)) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal v1 : Exp) ∧ σ' = σ.initHeap l 1 (some v2) ∧ efs = [] := by
  cases hs with
  | xchgS _ v1' _ _ h' =>
    simp only [State.get?] at h'
    rw [h] at h'
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h'
    subst h'
    refine ⟨rfl, rfl, rfl, rfl⟩

theorem faaS_det {l : Loc} {i1 i2 : Int} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some (Val.lit (.int i1))))
    (hs : BaseStep (.faa (.val (.lit (.loc l))) (.val (.lit (.int i2)))) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.lit (.int i1)) : Exp) ∧
      σ' = σ.initHeap l 1 (some (Val.lit (.int (i1 + i2)))) ∧ efs = [] := by
  cases hs with
  | faaS _ i1' _ _ h' =>
    simp only [State.get?] at h'
    rw [h] at h'
    simp only [Option.some.injEq, Val.lit.injEq, BaseLit.int.injEq] at h'
    subst h'
    refine ⟨rfl, rfl, rfl, rfl⟩

theorem cmpXchgS_det_true {l : Loc} {v1 v2 vl : Val} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some vl)) (htrue : decide (vl = v1) = true)
    (hs : BaseStep (.cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2)) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.pair vl (.lit (.bool true))) : Exp) ∧
      σ' = σ.initHeap l 1 (some v2) ∧ efs = [] := by
  cases hs with
  | cmpXchgS _ _ _ vl' _ b' h' hcs' hb' =>
    simp only [State.get?] at h'
    rw [h] at h'
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h'
    subst h'
    rw [htrue] at hb'
    subst hb'
    refine ⟨rfl, rfl, rfl, rfl⟩

theorem cmpXchgS_det_false {l : Loc} {v1 v2 vl : Val} {σ : State} {obs e' σ' efs}
    (h : get? (M := HeapF) σ.heap l = some (some vl)) (hfalse : decide (vl = v1) = false)
    (hs : BaseStep (.cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2)) σ obs e' σ' efs) :
    obs = [] ∧ e' = (ToVal.ofVal (Val.pair vl (.lit (.bool false))) : Exp) ∧
      σ' = σ ∧ efs = [] := by
  cases hs with
  | cmpXchgS _ _ _ vl' _ b' h' hcs' hb' =>
    simp only [State.get?] at h'
    rw [h] at h'
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h'
    subst h'
    rw [hfalse] at hb'
    subst hb'
    refine ⟨rfl, rfl, rfl, rfl⟩

/-! ### Multi-cell allocation helpers (for the `allocN` branch).

`allocN n v` writes `v` into `n` consecutive fresh locations. The state update
`State.initHeap` is a left-fold of single inserts; the lemmas below characterise
its heap pointwise and as a left-biased union with a freshly-built block
`allocCells`, which is what lets `genHeap_alloc_big` produce the new points-to and
meta tokens. -/

/-- A block of `n` cells all holding `v`, starting at `l` (`l, l+1, …, l+(n-1)`).
This is `(State.initHeap σ l n v).heap` with the existing heap `σ.heap` removed. -/
def allocCells (l : Loc) (n : Nat) (v : Option Val) : HeapF (Option Val) :=
  (List.range n).foldl (fun h (i : Nat) => Std.insert (M := HeapF) h (l + (i : Int)) v) ∅

theorem get?_foldl_insert (l : Loc) (v : Option Val) (m : HeapF (Option Val)) (n : Nat) (k : Loc) :
    get? (M := HeapF) ((List.range n).foldl
        (fun h (i : Nat) => Std.insert (M := HeapF) h (l + (i : Int)) v) m) k
      = if (∃ i, i < n ∧ k = l + (i : Int)) then some v else get? (M := HeapF) m k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Iris.Std.LawfulPartialMap.get?_insert, ih]
    by_cases hk : (l + (n : Int)) = k
    · rw [if_pos hk, if_pos ⟨n, Nat.lt_succ_self n, hk.symm⟩]
    · rw [if_neg hk]
      by_cases hex : ∃ i, i < n ∧ k = l + (i : Int)
      · obtain ⟨i, hi, hki⟩ := hex
        rw [if_pos ⟨i, hi, hki⟩, if_pos ⟨i, Nat.lt_succ_of_lt hi, hki⟩]
      · rw [if_neg hex, if_neg]
        rintro ⟨i, hi, hki⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact hex ⟨i, hi', hki⟩
        · exact hk hki.symm

theorem get?_allocCells {l : Loc} {n : Nat} {v : Option Val} {k : Loc} :
    get? (M := HeapF) (allocCells l n v) k
      = if (∃ i, i < n ∧ k = l + (i : Int)) then some v else none := by
  rw [allocCells, get?_foldl_insert]
  simp only [LawfulPartialMap.get?_empty]

/-- `State.initHeap` is the left-biased union of the fresh block with the old heap. -/
theorem initHeap_heap_eq {σ : State} {l : Loc} {n : Int} {v : Option Val} :
    Iris.Std.PartialMap.equiv (M := HeapF) (σ.initHeap l n v).heap
      (Iris.Std.PartialMap.union (allocCells l n.toNat v) σ.heap) := by
  intro k
  show get? (M := HeapF) ((List.range n.toNat).foldl
      (fun h (i : Nat) => Std.insert (M := HeapF) h (l + (i : Int)) v) σ.heap) k = _
  rw [get?_foldl_insert, Iris.Std.LawfulPartialMap.get?_union, get?_allocCells]
  by_cases hex : ∃ i, i < n.toNat ∧ k = l + (i : Int)
  · simp only [if_pos hex, Option.orElse]
  · simp only [if_neg hex, Option.orElse]

theorem allocCells_disjoint {l : Loc} {n : Int} {v : Val} {m : HeapF (Option Val)}
    (hf : ∀ i : Int, 0 ≤ i → i < n → get? (M := HeapF) m (l + i) = none) :
    Std.PartialMap.disjoint (M := HeapF) (allocCells l n.toNat (some v)) m := by
  intro k ⟨h1, h2⟩
  rw [get?_allocCells] at h1
  split at h1 <;> rename_i hcond
  · obtain ⟨i, hi, hki⟩ := hcond
    rw [hki, hf (i : Int) (Int.natCast_nonneg i) (by omega)] at h2
    simp at h2
  · simp at h1

private theorem mem_le_foldr_max (x : Int) (L : List Int) (h : x ∈ L) :
    x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- Any heap has a fresh block of `n` consecutive locations: pick a base strictly
above every used location's address. This is the reducibility witness for the
`allocN` lift, replacing Rocq's built-in `fresh_locs`. -/
theorem exists_fresh_block (m : HeapF (Option Val)) (n : Int) :
    ∃ l : Loc, ∀ i : Int, 0 ≤ i → i < n → get? (M := HeapF) m (l + i) = none := by
  refine ⟨Loc.mk ((m.keys.map Loc.n).foldr max 0 + 1), fun i hi0 hin => ?_⟩
  have hnotmem : (Loc.mk ((m.keys.map Loc.n).foldr max 0 + 1) + i) ∉ m.keys := by
    intro hmem
    have hle : (Loc.mk ((m.keys.map Loc.n).foldr max 0 + 1) + i).n
        ≤ (m.keys.map Loc.n).foldr max 0 :=
      mem_le_foldr_max _ _ (List.mem_map_of_mem hmem)
    simp only [loc_add_n] at hle
    omega
  simpa [get?, getElem?_eq_none_iff, ← Std.ExtTreeMap.mem_keys] using hnotmem

private theorem coPset_top_ne_empty : (⊤ : CoPset) ≠ ∅ := by
  intro h
  have hm : Pos.xH ∈ (⊤ : CoPset) := CoPset.mem_full
  rw [h] at hm
  exact CoPset.mem_empty hm

/-- The heap-only completeness equation: case analysis on the base step. Mirrors
`wp_base_completeness` in `case_studies/heaplang/completeness_generic.v`. -/
theorem wp_base_completeness (e₁ : Exp) (σ : State) (E : CoPset)
    (Hred : BaseStep.Reducible (e₁, σ)) :
    heap_inv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e₁ σ E) := by
  iintro Hinv
  obtain ⟨κ, e', σ', efs, Hstep⟩ := Hred
  cases Hstep with
  | recS f x e σ =>
      iapply (wp_base_pure instPureExecRec trivial σ E (fun σ' => BaseStep.recS f x e σ')) $$ Hinv
  | pairS v1 v2 σ =>
      iapply (wp_base_pure PureExec_pair trivial σ E (fun σ' => BaseStep.pairS v1 v2 σ')) $$ Hinv
  | injLS v σ =>
      iapply (wp_base_pure PureExec_injl trivial σ E (fun σ' => BaseStep.injLS v σ')) $$ Hinv
  | injRS v σ =>
      iapply (wp_base_pure PureExec_injr trivial σ E (fun σ' => BaseStep.injRS v σ')) $$ Hinv
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
      iapply (wp_base_pure instPureExecCaseInjl trivial σ E (fun σ' => BaseStep.caseLS v et ee σ')) $$ Hinv
  | caseRS v et ee σ =>
      iapply (wp_base_pure instPureExecCaseInjr  trivial σ E (fun σ' => BaseStep.caseRS v et ee σ')) $$ Hinv
  | loadS l v σ hl =>
      iapply (wp_base_atomic_nochange (v₂ := v) l v σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.loadS l v σ hl)) hl
        (fun σ'' h => BaseStep.loadS l v σ'' h) loadS_det) $$ Hinv
  | storeS l v w σ hl =>
      iapply (wp_base_atomic (v₂ := .lit .unit) l v (some w) σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.storeS l v w σ hl)) hl
        (fun σ'' h => BaseStep.storeS l v w σ'' h) (fun _ hs => storeS_det hs)) $$ Hinv
  | freeS l v σ hl =>
      iapply (wp_base_atomic (v₂ := .lit .unit) l v none σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.freeS l v σ hl)) hl
        (fun σ'' h => BaseStep.freeS l v σ'' h) (fun _ hs => freeS_det hs)) $$ Hinv
  | xchgS l v1 v2 σ hl =>
      iapply (wp_base_atomic (v₂ := v1) l v1 (some v2) σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.xchgS l v1 v2 σ hl)) hl
        (fun σ'' h => BaseStep.xchgS l v1 v2 σ'' h) xchgS_det) $$ Hinv
  | faaS l i1 i2 σ hl =>
      iapply (wp_base_atomic (v₂ := .lit (.int i1)) l (.lit (.int i1))
        (some (.lit (.int (i1 + i2)))) σ E
        (base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.faaS l i1 i2 σ hl)) hl
        (fun σ'' h => BaseStep.faaS l i1 i2 σ'' h) faaS_det) $$ Hinv
  | cmpXchgS l v1 v2 vl σ b hl hcs hb =>
      cases hb1 : decide (vl = v1) with
      | true =>
          iapply (wp_base_atomic (v₂ := .pair vl (.lit (.bool true))) l vl (some v2) σ E
            (base_step_to_val_atomic Atomicity.StronglyAtomic
              (BaseStep.cmpXchgS l v1 v2 vl σ true hl hcs (by rw [hb1])))
            hl
            (fun σ'' h => by
              have := BaseStep.cmpXchgS l v1 v2 vl σ'' true h hcs (by rw [hb1])
              simpa using this)
            (fun h hs => cmpXchgS_det_true h hb1 hs)) $$ Hinv
      | false =>
          iapply (wp_base_atomic_nochange (v₂ := .pair vl (.lit (.bool false))) l vl σ E
            (base_step_to_val_atomic Atomicity.StronglyAtomic
              (BaseStep.cmpXchgS l v1 v2 vl σ false hl hcs (by rw [hb1])))
            hl
            (fun σ'' h => by
              have := BaseStep.cmpXchgS l v1 v2 vl σ'' false h hcs (by rw [hb1])
              simpa using this)
            (fun h hs => cmpXchgS_det_false h hb1 hs)) $$ Hinv
  | forkS e σ =>
      -- Fork lands in the non-atomic disjunct: the forked thread `e` becomes the
      -- single forked expression `efs = [e]`, and the parent steps to `#()`.
      imodintro
      iright
      iframe Hinv
      iintro %Φ %E₂ H
      iapply wp_fork_fupd
      iintro !>
      ihave Htraj : iprop(∀ σ₁, heap_inv σ₁ ={E}=∗
          ∃ κ σ₁', ⌜PrimSteps (.fork e) σ₁ κ (.val (.lit .unit)) σ₁' [e]⌝ ∗ heap_inv σ₁') $$ []
      · iintro %σ₁ Hheap
        imodintro
        iexists [], σ₁
        iframe Hheap
        ipureintro
        exact PrimSteps.once (EctxLanguage.primStep_of_baseStep (BaseStep.forkS e σ₁))
      imod H $$ Htraj with ⟨HwpUnit, Hefs⟩
      isplitl [Hefs]
      · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hefs
      · iapply (wp_value_fupd' (v := .lit .unit)).1 $$ HwpUnit
  | allocNS n v σ l hn hfresh =>
      -- `allocN` is atomic and allocates a fresh block of `n` cells.
      imodintro
      ileft
      have hatom : Atomic Atomicity.StronglyAtomic (Exp.allocN (.val (.lit (.int n))) (.val v)) :=
        base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.allocNS n v σ l hn hfresh)
      iframe %hatom
      iintro %Φ Hstep
      iapply wp_lift_atomic_step
        (EctxLanguage.val_stuck (BaseStep.allocNS n v σ l hn hfresh))
      iintro %σ₁ %ns %obs %obs' %nt Hσ !>
      icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
      -- Reducibility in `σ₁` from a fresh block.
      obtain ⟨lf, hlf⟩ := exists_fresh_block σ₁.heap n
      have Hred₁ : BaseStep.Reducible (Exp.allocN (.val (.lit (.int n))) (.val v), σ₁) :=
        ⟨[], _, _, [], BaseStep.allocNS n v σ₁ lf hn hlf⟩
      isplitr
      · ipureintro
        simp only [Stuckness.MaybeReducible]
        exact EctxLanguage.primStep_reducible_of_baseStep_reducible Hred₁
      iintro !> %e₂ %σ₂ %eₜ %Hprim Hcr
      cases EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred₁ Hprim
      rename_i l' Hpo Hi
      ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
      -- Destructure `heap_inv σ` into its heap and prophecy conjuncts.
      icases Hinv with ⟨Hmap, Hproph_inv⟩
      -- Allocate the new block in the state interpretation.
      imod (genHeap_alloc_big (allocCells l' n.toNat (some v)) σ₁.heap (allocCells_disjoint Hi))
        $$ Hσ with ⟨Hσ', Hnewpts, Hnewmeta⟩
      -- Freshness of the block in `σ` (the `heap_inv` state), via `meta_token_ne`.
      ihave %hfreshσ : ⌜∀ i : Int, 0 ≤ i → i < n → get? (M := HeapF) σ.heap (l' + i) = none⌝
          $$ [Hmap Hnewmeta]
      · iintro %i %hi0 %hin
        rcases hgc : get? (M := HeapF) σ.heap (l' + i) with _ | vo
        · itrivial
        · icases (BigSepM.bigSepM_lookup_acc (M := HeapF)
            (Φ := fun (k : Loc) (vo : Option Val) => iprop(heapCellPts k vo ∗ metaToken k ⊤)) hgc).1
            $$ Hmap with ⟨⟨_, Hmeta1⟩, _⟩
          have hcell_new : get? (M := HeapF) (allocCells l' n.toNat (some v)) (l' + i)
              = some (some v) := by
            rw [get?_allocCells, if_pos ⟨i.toNat, by omega, by rw [Int.toNat_of_nonneg hi0]⟩]
          icases (BigSepM.bigSepM_lookup_acc (M := HeapF)
            (Φ := fun (k : Loc) (_vo : Option Val) => iprop(metaToken k ⊤)) hcell_new).1
            $$ Hnewmeta with ⟨Hmeta2, _⟩
          icases metaToken_ne coPset_top_ne_empty $$ Hmeta1 Hmeta2 with %hne
          exact absurd rfl hne
      -- Instantiate the magic premise with the base step from `σ` at `l'`.
      imod Hstep $$ [] with ⟨Hpost, _⟩
      · ipureintro
        exact EctxLanguage.primStep_of_baseStep (BaseStep.allocNS n v σ l' hn hfreshσ)
      imodintro
      isplitl [Hσ' Hproph]
      · simp only [stateInterp]
        isplitl [Hσ']
        · iapply genHeapInterp_eqv (Iris.Std.PartialMap.equiv.symm _ _ initHeap_heap_eq)
          iexact Hσ'
        · iexact Hproph
      isplitl [Hpost Hmap Hproph_inv Hnewpts Hnewmeta]
      · iexists (.lit (.loc l'))
        isplit
        · ipureintro; simp [toVal]
        iapply Hpost
        simp only [heap_inv]
        isplitl [Hmap Hnewpts Hnewmeta]
        · iapply (BigSepM.bigSepM_eqv_of_perm
            (Φ := fun (k : Loc) (vo : Option Val) => iprop(heapCellPts k vo ∗ metaToken k ⊤))
            initHeap_heap_eq).2
          iapply (BigSepM.bigSepM_union
            (Φ := fun (k : Loc) (vo : Option Val) => iprop(heapCellPts k vo ∗ metaToken k ⊤))
            (allocCells_disjoint hfreshσ)).2
          isplitl [Hnewpts Hnewmeta]
          · iapply (Iris.BI.equiv_iff.mp (BigSepM.bigSepM_sep_eqv (M := HeapF)
              (Φ := fun (k : Loc) (vo : Option Val) => heapCellPts k vo)
              (Ψ := fun (k : Loc) (_vo : Option Val) => iprop(metaToken k ⊤)))).2
            -- Convert the raw points-tos of the freshly-allocated (live) cells
            -- into cell invariants before framing.
            ihave Hnewpts := (BigSepM.bigSepM_mono_of_forall
              (fun {k vo} => pointsTo_heapCellPts k vo)) $$ Hnewpts
            iframe Hnewpts Hnewmeta
          · iexact Hmap
        · iexact Hproph_inv
      · itrivial
  | newProphS σ p hp =>
      -- `newProph` is atomic and allocates a fresh prophecy variable.
      imodintro
      ileft
      have hatom : Atomic Atomicity.StronglyAtomic (Exp.newProph : Exp) :=
        base_step_to_val_atomic Atomicity.StronglyAtomic (BaseStep.newProphS σ p hp)
      iframe %hatom
      iintro %Φ Hstep
      iapply wp_lift_atomic_step
        (EctxLanguage.val_stuck (BaseStep.newProphS σ p hp))
      iintro %σ₁ %ns %obs %obs' %nt Hσ !>
      icases (stateInterp_split σ₁ ns (obs ++ obs') nt).mp $$ Hσ with ⟨Hσ, Hproph⟩
      -- Pick a prophecy id fresh in `σ₁.usedProphId`.
      obtain ⟨pf, Hpf⟩ := Iris.Std.List.fresh σ₁.usedProphId.toList
      have Hpf_contains : ¬ σ₁.usedProphId.contains pf := by
        intro hc; exact Hpf (Std.ExtTreeSet.mem_toList.mpr hc)
      have Hred₁ : BaseStep.Reducible (Exp.newProph, σ₁) :=
        ⟨[], _, _, [], BaseStep.newProphS σ₁ pf Hpf_contains⟩
      isplitr
      · ipureintro
        simp only [Stuckness.MaybeReducible]
        exact EctxLanguage.primStep_reducible_of_baseStep_reducible Hred₁
      iintro !> %e₂ %σ₂ %eₜ %Hprim Hcr
      cases EctxLanguage.baseStep_of_primStep_of_baseStep_reducible Hred₁ Hprim
      rename_i p' Hp'
      ihave Hproph := (prophMapInterp_nil_append obs' σ₁.usedProphId).mp $$ Hproph
      have Hp'_mem : p' ∉ σ₁.usedProphId :=
        fun hmem => Hp' (Std.ExtTreeSet.mem_iff_contains.symm.mp hmem)
      imod (ProphMap.new_proph p' σ₁.usedProphId obs' Hp'_mem) $$ Hproph
        with ⟨Hproph', Htok⟩
      -- Destructure `heap_inv σ` and derive that `p'` is fresh in `σ` via
      -- `proph_exclusive` against `Hproph_inv`.
      icases Hinv with ⟨Hmap, Hproph_inv⟩
      ihave %Hfresh_σ : ⌜p' ∉ σ.usedProphId⌝ $$ [Hproph_inv Htok]
      · iintro %hmem
        icases Iris.BI.BigSepS.bigSepS_elem_of_acc hmem $$ Hproph_inv with ⟨⟨%pvs', Htok'⟩, _⟩
        iapply proph_exclusive $$ Htok Htok'
      have Hfresh_σ_contains : ¬ σ.usedProphId.contains p' := fun hc =>
        Hfresh_σ (Std.ExtTreeSet.mem_iff_contains.symm.mpr hc)
      -- Instantiate the magic premise with the `newProph` step from `σ` at `p'`.
      imod Hstep $$ [] with ⟨Hpost, _⟩
      · ipureintro
        exact EctxLanguage.primStep_of_baseStep (BaseStep.newProphS σ p' Hfresh_σ_contains)
      imodintro
      isplitl [Hσ Hproph']
      · simp only [stateInterp]
        iframe Hσ
        rw [show ({p'} ∪ σ₁.usedProphId : Std.ExtTreeSet ProphId compare)
            = σ₁.usedProphId.insert p' from usedProph_insert_eq.symm]
        iexact Hproph'
      isplitl [Hpost Hmap Hproph_inv Htok]
      · iexists (.lit (.prophecy p'))
        isplit
        · ipureintro; simp [toVal]
        iapply Hpost
        simp only [heap_inv]
        isplitl [Hmap]
        · iexact Hmap
        · -- goal: bigSepS (σ.usedProphId.insert p') (∃ pvs, proph)
          rw [usedProph_insert_eq (ps := σ.usedProphId) (p := p')]
          have hdisj : ({p'} : Std.ExtTreeSet ProphId compare) ## σ.usedProphId := by
            intro x ⟨h1, h2⟩
            rw [Iris.Std.LawfulSet.mem_singleton] at h1
            subst h1
            exact Hfresh_σ h2
          iapply (Iris.BI.BigSepS.bigSepS_union hdisj).mpr
          isplitl [Htok]
          · iapply Iris.BI.BigSepS.bigSepS_singleton.mpr
            iexists (prophListResolves obs' p')
            iexact Htok
          · iexact Hproph_inv
      · itrivial
  | resolveS p v e σ w σ' κs ts hbase hp =>
      -- Mirror of `completeness_generic.v:127–159`. Resolve is atomic since the
      -- inner step `hbase` produces a value in one base step. We recurse on
      -- `hbase` to get the completeness equation for `e`, then lift through
      -- the `Resolve` wrapper via `wp_resolve_strong`.
      have IH : heap_inv (GF := GF) σ ⊢ iprop(|={E}=> baseCompletenessGoal e σ E) :=
        wp_base_completeness e σ E ⟨κs, _, _, _, hbase⟩
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
      iframe %hatom
      iintro %Φ Hstep
      icases Hinv with ⟨Hmap, Hproph_inv⟩
      icases Iris.BI.BigSepS.bigSepS_elem_of_acc hp_mem $$ Hproph_inv
        with ⟨⟨%pvs, Htok⟩, HcloseProph⟩
      iapply (wp_resolve_strong hatom_e hne_e) $$ Htok
      iintro Hele
      ihave Hinv_full : iprop(heap_inv σ) $$ [Hmap HcloseProph Hele]
      · unfold heap_inv
        iframe Hmap
        iapply HcloseProph
        iexists pvs; iexact Hele
      ihave Hinner : iprop(|={E}=> baseCompletenessGoal e σ E) $$ [Hinv_full]
      · iapply IH; iexact Hinv_full
      iapply fupd_wp
      imod Hinner with H
      imodintro
      icases H with (⟨_hatom_e', Hrst⟩ | ⟨Hinv_back, Hrst_nonatom⟩)
      · -- Atomic disjunct: feed `Hrst` the resolve-strong post for `e`.
        iapply Hrst
        iintro !> %κ_e %v_e %σ_e %efs_e %Hprim_e
        have Hbase_e : BaseStep e σ κ_e (.val v_e) σ_e efs_e :=
          primStep_val_baseStep Hprim_e
        imod Hstep $$ %_ %_ %_ %_ %(prim_step_resolve_of_inner (w := w) Hbase_e hp)
          with ⟨Hwp_outer, Hefs⟩
        imodintro
        iframe Hefs
        iintro ⟨Hmap_e, Hproph_inv_e⟩
        have hp_mem_e : p ∈ σ_e.usedProphId :=
          base_step_more_proph_ids Hbase_e p hp_mem
        icases Iris.BI.BigSepS.bigSepS_elem_of_acc hp_mem_e $$ Hproph_inv_e
          with ⟨⟨%pvs2, Hele2⟩, HcloseProph_e⟩
        iexists pvs2
        iframe Hele2
        iintro %pvs'' %heq Hele2'
        subst heq
        iapply Hwp_outer
        unfold heap_inv
        iframe Hmap_e
        iapply HcloseProph_e
        iexists pvs''; iexact Hele2'
      · -- Non-atomic disjunct: symmetric to the atomic case, plus extracting
        -- the single prim step from the trajectory via `primSteps_atomic`.
        iapply Hrst_nonatom
        iintro !> %e₂_e %efs_e Htraj_e
        imod Htraj_e $$ %_ Hinv_back with ⟨%κ_e, %σ_e, %Hprims, ⟨Hmap_e, Hproph_inv_e⟩⟩
        obtain ⟨Hprim_e, hval_e⟩ :=
          ProgramLogic.primSteps_atomic (e := e) hatom_e Hprims
        obtain ⟨v_e, rfl⟩ : ∃ v_e, e₂_e = Exp.val v_e := by
          match e₂_e, hval_e with
          | .val v_e, _ => exact ⟨v_e, rfl⟩
        have Hbase_e : BaseStep e σ κ_e (.val v_e) σ_e efs_e :=
          primStep_val_baseStep Hprim_e
        imod Hstep $$ %_ %_ %_ %_ %(prim_step_resolve_of_inner (w := w) Hbase_e hp)
          with ⟨Hwp_outer, Hefs⟩
        imodintro
        have hp_mem_e : p ∈ σ_e.usedProphId :=
          base_step_more_proph_ids Hbase_e p hp_mem
        icases Iris.BI.BigSepS.bigSepS_elem_of_acc hp_mem_e $$ Hproph_inv_e
          with ⟨⟨%pvs2, Hele2⟩, HcloseProph_e⟩
        isplitl [Hele2 Hwp_outer Hmap_e HcloseProph_e]
        · -- WP (Val v_e) {{ strong-post }} — apply wp_value', witness pvs2.
          iapply wp_value'
          iexists pvs2
          iframe Hele2
          iintro %pvs'' %heq Hele2'
          subst heq
          iapply Hwp_outer
          unfold heap_inv
          iframe Hmap_e
          iapply HcloseProph_e
          iexists pvs''; iexact Hele2'
        · iexact Hefs
termination_by e₁

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
  heap_inv_timeless _C σ := heap_inv_timeless σ
  ectx_lang_completeness n _C e₁ σ K E := wp_base_completeness_actual n _C e₁ σ K E

end Framework

section Endpoint

/-- **Top-level heap-lang completeness**: an adequate program admits a WP with the
adequacy postcondition. Mirrors `heap_lang_sem_completeness` in
`case_studies/heaplang/completeness_classical.v`. -/
theorem heap_lang_sem_completeness {H : Type _ → Type _} [LawfulFiniteMap H Nat]
    [GhostMapG GF Nat Exp H] [CInvG GF]
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
    [GhostMapG GF Nat Exp H] [CInvG GF]
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
