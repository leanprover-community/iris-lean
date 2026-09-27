/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.HeapLang.TransfiniteProofMode
public import Iris.Instances.Lib.GhostMap
public import Iris.ProgramLogic.Refinement.NatSource
public import Iris.ProgramLogic.Refinement.SeqWeakestPre
public import Iris.Instances.Lib.NaInvariantsTransfinite

/-! # Refinements between heap_lang programs

This file ports `theories/examples/refinements/refinement.v` of Transfinite Iris: the refinement
logic for proving that a heap_lang program `t` (the target) refines a heap_lang program `s` (the
source): every result of `t` is related to a result of `s`, and `t` terminates if `s` does
(`heap_lang_ref_adequacy`).

The source is heap_lang itself, with a stuttering budget (the lexicographic product with the
natural numbers `natA`). Its ghost state consists of three ghost maps (instead of the
`auth (gmap nat (excl expr) × gen_heap)` camera and the monotone list of the Rocq development):
the thread pool `j ⤇ e`, the source heap `l ↦s v` and the execution trace of the source (whose
persistent elements `traceIdx i c` record that `c` is a configuration of the source execution).
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.Transfinite.Refinement

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language
open Language.Notation Relation

/-! ## Lists of steps -/

/-- Rocq: `rtc_list`. -/
inductive RtcList {A : Type _} (R : A → A → Prop) : List A → Prop
  | nil : RtcList R []
  | once (x : A) : RtcList R [x]
  | cons (x y : A) (l : List A) : R x y → RtcList R (y :: l) → RtcList R (x :: y :: l)

/-- Rocq: `rtc_list_r`. -/
theorem RtcList.snoc {A : Type _} {R : A → A → Prop} {x y : A} {l : List A} (hR : R x y)
    (h : RtcList R (l ++ [x])) : RtcList R (l ++ [x] ++ [y]) := by
  induction l with
  | nil =>
    exact .cons x y [] hR (.once y)
  | cons a l ih =>
    cases l with
    | nil =>
      cases h with
      | cons _ _ _ hab h' => exact .cons a x [y] hab (ih h')
    | cons b l =>
      cases h with
      | cons _ _ _ hab h' => exact .cons a b _ hab (ih h')

/-- Rocq: `rtc_list_lookup_last_rtc`. -/
theorem RtcList.lookup_rtc {A : Type _} {R : A → A → Prop} {x y : A} {l : List A} {i : Nat}
    (hi : (l ++ [y])[i]? = some x) (h : RtcList R (l ++ [y])) : FromMathlib.Relation.ReflTransGen R x y := by
  induction l generalizing i x with
  | nil =>
    cases i with
    | zero => cases hi; exact .refl
    | succ i => simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      cases hi
      cases l with
      | nil =>
        cases h with
        | cons _ _ _ hab _ => exact .single hab
      | cons b l =>
        cases h with
        | cons _ _ _ hab h' =>
          exact .head hab (ih (x := b) (i := 0) (by simp) h')
    | succ i =>
      cases l with
      | nil =>
        cases h with
        | cons _ _ _ _ h' => exact ih hi h'
      | cons b l =>
        cases h with
        | cons _ _ _ _ h' => exact ih hi h'

/-! ## Ghost state of the source -/

/-- Maps with natural-number keys. -/
abbrev NatMap := fun V => Std.ExtTreeMap Nat V compare

/-- Configurations of heap_lang. -/
abbrev Cfg := List Exp × State

/-- Values of the source heap (a wrapper, to distinguish the ghost map of the source heap from the
one of the target heap). -/
structure SrcVal where
  val : Option Val

/-- The ghost state of the refinement logic (Rocq: `rheapG`). -/
class RHeapG (GF : BundledGFunctors) extends HeapLangTGS GF where
  tpool : GhostMapG GF Nat Exp NatMap
  tpoolName : GName
  heapS : GhostMapG GF Loc SrcVal HeapF
  heapSName : GName
  trace : GhostMapG GF Nat Cfg NatMap
  traceName : GName

attribute [reducible, instance] RHeapG.tpool RHeapG.heapS RHeapG.trace

/-- A list as a map from indices (Rocq: `to_tpool`). -/
def toMapGo {V : Type _} : Nat → List V → NatMap V
  | _, [] => ∅
  | i, x :: xs => PartialMap.insert (toMapGo (i + 1) xs) i x

/-- Rocq: `to_tpool`. -/
def toMap {V : Type _} (l : List V) : NatMap V := toMapGo 0 l

theorem toMapGo_get? {V : Type _} (l : List V) (i j : Nat) :
    PartialMap.get? (toMapGo i l) (i + j) = l[j]? := by
  induction l generalizing i j with
  | nil => exact LawfulPartialMap.get?_empty _
  | cons x xs ih =>
    cases j with
    | zero => exact LawfulPartialMap.get?_insert_eq rfl
    | succ j =>
      rw [toMapGo, LawfulPartialMap.get?_insert_ne (by omega), show i + (j + 1) = i + 1 + j by omega,
        ih]
      rfl

theorem toMapGo_get?_lt {V : Type _} (l : List V) (i j : Nat) (h : j < i) :
    PartialMap.get? (toMapGo i l) j = none := by
  induction l generalizing i with
  | nil => exact LawfulPartialMap.get?_empty _
  | cons x xs ih =>
    rw [toMapGo, LawfulPartialMap.get?_insert_ne (by omega), ih _ (by omega)]

/-- Rocq: `tpool_lookup`. -/
theorem toMap_get? {V : Type _} (l : List V) (j : Nat) : PartialMap.get? (toMap l) j = l[j]? := by
  have := toMapGo_get? l 0 j
  simpa [toMap] using this

theorem toMap_ext {V : Type _} {m : NatMap V} {l : List V}
    (h : ∀ j, PartialMap.get? m j = l[j]?) : m = toMap l :=
  LawfulPartialMap.equiv_iff_eq.mp fun j => by rw [h, toMap_get?]

/-- Rocq: `to_tpool_insert`. -/
theorem toMap_set {V : Type _} (l : List V) (j : Nat) (x : V) (hj : j < l.length) :
    toMap (l.set j x) = PartialMap.insert (toMap l) j x :=
  (toMap_ext fun i => by
    by_cases hij : j = i
    · subst hij; rw [LawfulPartialMap.get?_insert_eq rfl]; simp [hj]
    · rw [LawfulPartialMap.get?_insert_ne hij, toMap_get?, List.getElem?_set_ne hij]).symm

/-- Rocq: `to_tpool_snoc`. -/
theorem toMap_snoc {V : Type _} (l : List V) (x : V) :
    toMap (l ++ [x]) = PartialMap.insert (toMap l) l.length x :=
  (toMap_ext fun i => by
    by_cases hij : l.length = i
    · subst hij; rw [LawfulPartialMap.get?_insert_eq rfl]; simp
    · rw [LawfulPartialMap.get?_insert_ne hij, toMap_get?]
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · rw [List.getElem?_eq_none (by omega : l.length ≤ i),
          List.getElem?_eq_none (by simp; omega : (l ++ [x]).length ≤ i)]
      · rw [List.getElem?_append_left h]).symm

theorem toMap_get?_length {V : Type _} (l : List V) :
    PartialMap.get? (toMap l) l.length = none := by
  rw [toMap_get?]; simp

variable {GF : BundledGFunctors} [G : RHeapG GF]

/-- The source heap as a map of `SrcVal`s. -/
def srcHeap (h : HeapF (Option Val)) : HeapF SrcVal := Std.PartialMap.map SrcVal.mk h

/-- Source points-to (Rocq: `l ↦s{q} v`). -/
def heapSPointsTo (l : Loc) (q : DFrac) (v : Val) : IProp GF :=
  ghost_map_elem G.heapSName q l (SrcVal.mk (some v))

/-- Source threads (Rocq: `j ⤇ e`). -/
def tpoolPointsTo (j : Nat) (e : Exp) : IProp GF := ghost_map_elem G.tpoolName (.own 1) j e

/-- A configuration of the source execution (Rocq: `fmlist_idx`). -/
def traceIdx (i : Nat) (c : Cfg) : IProp GF := ghost_map_elem G.traceName .discard i c

instance heapSPointsTo_timeless (l : Loc) (q : DFrac) (v : Val) :
    Timeless (heapSPointsTo (GF := GF) l q v) := by
  unfold heapSPointsTo; infer_instance

instance traceIdx_persistent (i : Nat) (c : Cfg) : Persistent (traceIdx (GF := GF) i c) := by
  unfold traceIdx; infer_instance

/-- The interpretation of the source configuration (Rocq: `source_interp` of
`heap_lang_source`). -/
def cfgInterp (c : Cfg) : IProp GF :=
  iprop(ghost_map_auth G.tpoolName (.own 1) (toMap c.1) ∗
    ghost_map_auth G.heapSName (.own 1) (srcHeap c.2.heap) ∗
    ∃ l : List Cfg, ⌜RtcList ErasedStep (l ++ [c])⌝ ∗
      ghost_map_auth G.traceName (.own 1) (toMap (l ++ [c])) ∗ traceIdx l.length c)

/-- heap_lang as a source (Rocq: `heap_lang_source`). -/
instance heapLangSource : Source GF Cfg where
  rel := ErasedStep
  interp := cfgInterp

/-- Rocq: `step_insert`. -/
theorem step_set {tp : List Exp} {j : Nat} {e e' : Exp} {σ σ' : State} {κ : List Observation}
    {efs : List Exp} (hj : tp[j]? = some e) (hstep : (e, σ) -<κ>-> (e', σ', efs)) :
    ErasedStep (tp, σ) (tp.set j e' ++ efs, σ') := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  refine ⟨κ, ?_⟩
  have h1 : tp.take j ++ tp[j] :: tp.drop (j + 1) = tp := by
    simp
  have h2 : tp.set j e' ++ efs = tp.take j ++ e' :: tp.drop (j + 1) ++ efs := by
    rw [List.set_eq_take_append_cons_drop, ite_eq_left hlt]
  have key := Step.atomic hstep (tp.take j) (tp.drop (j + 1))
  rw [h1] at key
  rw [h2]
  exact key

/-! ## Source steps -/

section Steps

open FromMathlib.Relation

theorem srcHeap_get? {h : HeapF (Option Val)} {l : Loc} {w : SrcVal}
    (hl : PartialMap.get? (srcHeap h) l = some w) : PartialMap.get? h l = some w.val := by
  unfold srcHeap at hl
  rw [Std.LawfulPartialMap.get?_map] at hl
  cases hh : PartialMap.get? h l with
  | none => simp [hh] at hl
  | some x => simp [hh] at hl; subst hl; rfl

theorem srcHeap_insert (h : HeapF (Option Val)) (l : Loc) (v : Option Val) :
    PartialMap.insert (srcHeap h) l (SrcVal.mk v) = srcHeap (PartialMap.insert h l v) := by
  unfold srcHeap
  exact Std.LawfulPartialMap.map_insert.symm

theorem srcHeap_get?_none {h : HeapF (Option Val)} {l : Loc}
    (hl : PartialMap.get? h l = none) : PartialMap.get? (srcHeap h) l = none := by
  unfold srcHeap
  rw [Std.LawfulPartialMap.get?_map, hl]
  rfl

/-- A step of the thread `j` of the source (the core of the operational rules). -/
theorem cfg_step (E : CoPset) (j : Nat) (e e' : Exp) (R Q : IProp GF)
    (H : ∀ σ : State, ghost_map_auth G.heapSName (.own 1) (srcHeap σ.heap) ∗ R ⊢
      |==> ∃ σ' : State, ⌜(e, σ) -<[]>-> (e', σ', [])⌝ ∗
        ghost_map_auth G.heapSName (.own 1) (srcHeap σ'.heap) ∗ Q) :
    tpoolPointsTo j e ∗ R ⊢ srcUpdate (src := heapLangSource) E iprop(tpoolPointsTo j e' ∗ Q) := by
  unfold srcUpdate tpoolPointsTo
  delta heapLangSource
  dsimp only
  unfold cfgInterp
  iintro ⟨Hj, HR⟩ %⟨tp, σ⟩ ⟨Htp, Hh, %l, %hrtc, Htr, -⟩
  icases ghost_map_lookup $$ Htp Hj with %hlook
  rw [toMap_get?] at hlook
  have hlen : j < tp.length := (List.getElem?_eq_some_iff.mp hlook).1
  imod H σ $$ [Hh HR] with ⟨%σ', %hstep, Hh, HQ⟩
  · iframe
  imod ghost_map_update e' $$ Htp Hj with ⟨Htp, Hj⟩
  have hstep' := step_set hlook hstep
  rw [List.append_nil] at hstep'
  imod ghost_map_insert_persist (l ++ [(tp, σ)]).length (tp.set j e', σ') (toMap_get?_length _)
    $$ Htr with ⟨Htr, #Hidx⟩
  imodintro
  iexists (tp.set j e', σ')
  isplitr
  · ipureintro
    exact .single hstep'
  rw [← toMap_set tp j e' hlen, ← toMap_snoc]
  unfold traceIdx
  iframe
  isplitr
  · ipureintro
    exact RtcList.snoc hstep' hrtc
  iexact Hidx

/-- A step of the thread `j` of the source whose result depends on the state. -/
theorem cfg_step_dep (E : CoPset) (j : Nat) (e : Exp) (R : IProp GF) (Q : Exp → IProp GF)
    (H : ∀ σ : State, ghost_map_auth G.heapSName (.own 1) (srcHeap σ.heap) ∗ R ⊢
      |==> ∃ (e' : Exp) (σ' : State), ⌜(e, σ) -<[]>-> (e', σ', [])⌝ ∗
        ghost_map_auth G.heapSName (.own 1) (srcHeap σ'.heap) ∗ Q e') :
    tpoolPointsTo j e ∗ R ⊢
      srcUpdate (src := heapLangSource) E iprop(∃ e', tpoolPointsTo j e' ∗ Q e') := by
  unfold srcUpdate tpoolPointsTo
  delta heapLangSource
  dsimp only
  unfold cfgInterp
  iintro ⟨Hj, HR⟩ %⟨tp, σ⟩ ⟨Htp, Hh, %l, %hrtc, Htr, -⟩
  icases ghost_map_lookup $$ Htp Hj with %hlook
  rw [toMap_get?] at hlook
  have hlen : j < tp.length := (List.getElem?_eq_some_iff.mp hlook).1
  imod H σ $$ [Hh HR] with ⟨%e', %σ', %hstep, Hh, HQ⟩
  · iframe
  imod ghost_map_update e' $$ Htp Hj with ⟨Htp, Hj⟩
  have hstep' := step_set hlook hstep
  rw [List.append_nil] at hstep'
  imod ghost_map_insert_persist (l ++ [(tp, σ)]).length (tp.set j e', σ') (toMap_get?_length _)
    $$ Htr with ⟨Htr, #Hidx⟩
  imodintro
  iexists (tp.set j e', σ')
  isplitr
  · ipureintro
    exact .single hstep'
  rw [← toMap_set tp j e' hlen, ← toMap_snoc]
  unfold traceIdx
  isplitl [Htp Hh Htr]
  · iframe
    isplitr
    · ipureintro
      exact RtcList.snoc hstep' hrtc
    iexact Hidx
  iexists e'
  iframe

/-- A pure step is a primitive step without effects (Rocq: `pure_step_prim_step`). -/
theorem purePrimStep_primStep {e₁ e₂ : Exp} (h : e₁ -ᵖ-> e₂) (σ : State) :
    (e₁, σ) -<[]>-> (e₂, σ, []) := by
  obtain ⟨e', σ', efs, hstep⟩ := h.safe σ
  obtain ⟨-, rfl, rfl, rfl⟩ := h.deterministic hstep
  exact hstep

/-- Rocq: `step_pure` for heap_lang as a source. -/
theorem cfg_step_pure (E : CoPset) (j : Nat) (e₁ e₂ : Exp) (hp : e₁ -ᵖ-> e₂) :
    tpoolPointsTo (GF := GF) j e₁ ⊢ srcUpdate (src := heapLangSource) E (tpoolPointsTo j e₂) := by
  have H := cfg_step (GF := GF) E j e₁ e₂ emp emp fun σ => by
    iintro ⟨Hh, -⟩
    imodintro
    iexists σ
    iframe
    ipureintro
    exact purePrimStep_primStep hp σ
  iintro Hj
  iapply srcUpdate_mono (src := heapLangSource)
  isplitl [Hj]
  · iapply H
    iframe
  · iintro ⟨H, -⟩
    iexact H

end Steps

/-! ## The stuttering source -/

section Stuttering

open FromMathlib.Relation

variable [N : NatSourceG GF]

/-- The natural numbers as a source, with the ghost state of `natA` (the state is a plain `Nat`,
so that it lives in `Type`). -/
instance natSource : Source GF Nat where
  rel a b := b < a
  interp n := srcA (GF := GF) (⟨n⟩ : NatC SI)

/-- heap_lang with a stuttering budget as a source (Rocq: `source Σ (heap_srcT * nat)`). -/
abbrev refSrc : Source GF (Cfg × Nat) := lexSource heapLangSource natSource

/-- Stuttering credits (Rocq: `$ n` for `natA`). -/
abbrev stutter (n : Nat) : IProp GF := srcF (GF := GF) (⟨n⟩ : NatC SI)

/-- A source update of the refinement source (Rocq: `src_update`). -/
abbrev srcUpd (E : CoPset) (P : IProp GF) : IProp GF := srcUpdate (src := refSrc (GF := GF)) E P

/-- A weak source update of the refinement source (Rocq: `weak_src_update`). -/
abbrev weakSrcUpd (E : CoPset) (P : IProp GF) : IProp GF :=
  weakSrcUpdate (src := refSrc (GF := GF)) E P

/-- Rocq: `step_pure_cred`. A pure source step can allocate stuttering credits. -/
theorem step_pure_cred (k : Nat) (E : CoPset) (j : Nat) (e₁ e₂ : Exp) (hp : e₁ -ᵖ-> e₂) :
    tpoolPointsTo (GF := GF) j e₁ ⊢ srcUpd E iprop(tpoolPointsTo j e₂ ∗ stutter k) := by
  iintro Hj
  iapply srcUpdate_embed_l_strong
  isplitl [Hj]
  · iapply cfg_step_pure E j e₁ e₂ hp $$ Hj
  iintro %b Hb
  delta natSource
  dsimp only
  unfold stutter srcA srcF
  have hlu : ((⟨b⟩ : NatC SI), (UCMRA.unit : NatC SI)) ~l~> (⟨b + k⟩, ⟨k⟩) :=
    (local_update_unital_discrete _ _ _ _).mpr fun z _ hz =>
      ⟨trivial, NatC.ext (by
        have := congrArg NatC.n hz
        have hu : (UCMRA.unit : NatC SI).n = 0 := rfl
        simp only [NatC.op_n] at this ⊢; omega)⟩
  imod iOwn_update (ULift.update (Auth.auth_update_alloc hlu)) $$ Hb with Hb
  icases (iOwn_op (E := N.elem)).mp $$ Hb with ⟨Ha, Hf⟩
  imodintro
  iexists b + k
  iframe

/-- Rocq: `step_pure`. -/
theorem step_pure (E : CoPset) (j : Nat) (e₁ e₂ : Exp) (hp : e₁ -ᵖ-> e₂) :
    tpoolPointsTo (GF := GF) j e₁ ⊢ srcUpd E (tpoolPointsTo j e₂) := by
  iintro Hj
  iapply srcUpdate_embed_l
  iapply cfg_step_pure E j e₁ e₂ hp $$ Hj

/-- Rocq: `steps_pure`. -/
theorem steps_pure (n : Nat) (E : CoPset) (j : Nat) (e₁ e₂ : Exp)
    (h : Iterate PurePrimStep (n + 1) e₁ e₂) :
    tpoolPointsTo (GF := GF) j e₁ ⊢ srcUpd E (tpoolPointsTo j e₂) := by
  induction n generalizing e₁ with
  | zero =>
    obtain ⟨b, hst, hrest⟩ := Relation.Iterate.succ_head_inv h
    cases hrest
    exact step_pure E j _ _ hst
  | succ n ih =>
    obtain ⟨b, hst, hrest⟩ := Relation.Iterate.succ_head_inv h
    iintro Hj
    iapply srcUpdate_bind (src := refSrc (GF := GF))
    isplitl [Hj]
    · iapply step_pure E j _ _ hst $$ Hj
    · iintro Hj
      iapply ih _ hrest $$ Hj

/-- Rocq: `steps_pure_exec`. -/
theorem steps_pure_exec (E : CoPset) (j : Nat) (e₁ e₂ : Exp) {φ : Prop} {n : Nat}
    [hp : PureExec φ (n + 1) e₁ e₂] (hφ : φ) :
    tpoolPointsTo (GF := GF) j e₁ ⊢ srcUpd E (tpoolPointsTo j e₂) :=
  steps_pure n E j e₁ e₂ (hp.pureExec hφ)

/-- Rocq: `step_load`. -/
theorem step_load (E : CoPset) (j : Nat) (K : List ECtxItem) (l : Loc) (q : DFrac) (v : Val) :
    tpoolPointsTo (GF := GF) j (fill K hl(!v(#l))) ∗ heapSPointsTo l q v ⊢
      srcUpd E iprop(tpoolPointsTo j (fill K (v : Exp)) ∗ heapSPointsTo l q v) := by
  iintro H
  iapply srcUpdate_embed_l
  iapply cfg_step E j _ _ _ _ (fun σ => ?_) $$ H
  unfold heapSPointsTo
  iintro ⟨Hh, Hl⟩
  icases ghost_map_lookup $$ Hh Hl with %hl
  have hl' := srcHeap_get? hl
  imodintro
  iexists σ
  iframe
  ipureintro
  exact EctxLanguage.fill_primStep K (EctxLanguage.primStep_of_baseStep (HeapLang.BaseStep.loadS l v σ hl'))

/-- Rocq: `step_store`. -/
theorem step_store (E : CoPset) (j : Nat) (K : List ECtxItem) (l : Loc) (v v' : Val) :
    tpoolPointsTo (GF := GF) j (fill K hl(v(#l) ← &v)) ∗ heapSPointsTo l (.own 1) v' ⊢
      srcUpd E iprop(tpoolPointsTo j (fill K hl(#())) ∗ heapSPointsTo l (.own 1) v) := by
  iintro H
  iapply srcUpdate_embed_l
  iapply cfg_step E j _ _ _ _ (fun σ => ?_) $$ H
  unfold heapSPointsTo
  iintro ⟨Hh, Hl⟩
  icases ghost_map_lookup $$ Hh Hl with %hl
  have hl' := srcHeap_get? hl
  imod ghost_map_update (SrcVal.mk (some v)) $$ Hh Hl with ⟨Hh, Hl⟩
  imodintro
  iexists σ.initHeap l 1 (some v)
  rw [srcHeap_insert, State.initHeap_singleton]
  iframe
  ipureintro
  have : (fill K hl(v(#l) ← &v), σ) -<[]>-> (fill K hl(#()), σ.initHeap l 1 (some v), []) :=
    EctxLanguage.fill_primStep K (EctxLanguage.primStep_of_baseStep
      (HeapLang.BaseStep.storeS l v' v σ hl'))
  rwa [State.initHeap_singleton] at this

/-- Rocq: `step_alloc`. -/
theorem step_alloc (E : CoPset) (j : Nat) (K : List ECtxItem) (v : Val) :
    tpoolPointsTo (GF := GF) j (fill K hl(ref(&v))) ⊢
      srcUpd E iprop(∃ l : Loc, tpoolPointsTo j (fill K hl(#l)) ∗ heapSPointsTo l (.own 1) v) := by
  have H := cfg_step_dep (GF := GF) E j (fill K hl(ref(&v))) emp
    (fun e' => iprop(∃ l : Loc, ⌜e' = fill K hl(#l)⌝ ∗ heapSPointsTo l (.own 1) v)) fun σ => by
    iintro ⟨Hh, -⟩
    have hfresh : PartialMap.get? (M := HeapF) σ.heap (Loc.fresh σ.heap.keys) = none := by
      have := Loc.fresh_fresh σ.heap.keys (i := 0) (Int.le_refl 0)
      simp only [loc_add_zero] at this
      simpa [PartialMap.get?, getElem?_eq_none_iff, ← Std.ExtTreeMap.mem_keys] using this
    imod ghost_map_insert (Loc.fresh σ.heap.keys) (SrcVal.mk (some v)) (srcHeap_get?_none hfresh)
      $$ Hh with ⟨Hh, Hl⟩
    imodintro
    iexists fill K hl(#(Loc.fresh σ.heap.keys)), σ.initHeap (Loc.fresh σ.heap.keys) 1 (some v)
    rw [srcHeap_insert, State.initHeap_singleton]
    iframe Hh
    isplitr
    · ipureintro
      have : (fill K hl(ref(&v)), σ) -<[]>->
          (fill K hl(#(Loc.fresh σ.heap.keys)), σ.initHeap (Loc.fresh σ.heap.keys) 1 (some v), []) :=
        EctxLanguage.fill_primStep K (EctxLanguage.primStep_of_baseStep (alloc_fresh v 1 σ (by decide)))
      rwa [State.initHeap_singleton] at this
    iexists Loc.fresh σ.heap.keys
    isplitr
    · ipureintro; rfl
    unfold heapSPointsTo
    iexact Hl
  iintro Hj
  iapply srcUpdate_embed_l
  iapply srcUpdate_mono (src := heapLangSource)
  isplitl [Hj]
  · iapply H
    iframe
  · iintro ⟨%e', Hj, %l, %rfl, Hl⟩
    iexists l
    iframe

/-- Rocq: `step_stutter`. -/
theorem step_stutter (E : CoPset) (c : Nat) :
    stutter (GF := GF) (c + 1) ⊢ srcUpd E (stutter c) := by
  iintro H
  iapply srcUpdate_embed_r
  unfold srcUpdate
  delta natSource
  dsimp only
  unfold stutter srcA srcF
  iintro %n Hn
  ihave H := (iOwn_op (E := N.elem) (γ := N.name) (a1 := ULift.up (● (⟨n⟩ : NatC SI)))
    (a2 := ULift.up (◯ (⟨c + 1⟩ : NatC SI)))).mpr $$ [Hn H]
  · iframe
  ihave ⟨Hv, H⟩ := iOwn_valid_l $$ H
  icases internalCmraValid_discrete.mp $$ Hv with %Hv
  obtain ⟨⟨f, hf⟩, -⟩ := Auth.auth_both_valid_discrete.mp Hv
  have hn : n = c + 1 + f.n := congrArg NatC.n hf
  have hlu : ((⟨n⟩ : NatC SI), (⟨c + 1⟩ : NatC SI)) ~l~> (⟨c + f.n⟩, ⟨c⟩) := by
    refine (local_update_unital_discrete _ _ _ _).mpr fun z _ hz => ⟨trivial, ?_⟩
    have hz' : n = c + 1 + z.n := congrArg NatC.n hz
    exact NatC.ext (by simp only [NatC.op_n]; omega)
  imod iOwn_update (ULift.update (Auth.auth_update hlu)) $$ H with H
  icases (iOwn_op (E := N.elem)).mp $$ H with ⟨HA, HF⟩
  imodintro
  iexists c + f.n
  iframe
  ipureintro
  exact .single (by omega)

/-- Adding stuttering credits to the target of a trace that changes the configuration (Rocq:
`step_add_stutter`). -/
theorem add_stutter {c₁ c₂ : Cfg} {n m : Nat} (k : Nat)
    (h : TransGen (refSrc (GF := GF)).rel (c₁, n) (c₂, m)) (hne : c₁ ≠ c₂) :
    TransGen (refSrc (GF := GF)).rel (c₁, n) (c₂, m + k) := by
  generalize ha : (c₁, n) = a at h
  generalize hb : (c₂, m) = b at h
  induction h generalizing c₂ m with
  | single hab =>
    subst ha hb
    cases hab with
    | left _ _ hstep => exact .single (.left _ _ hstep)
    | right _ _ => exact absurd rfl hne
  | @tail x b' hax hxb ih =>
    subst hb
    rcases hxb with ⟨_, _, hstep⟩ | @⟨_, nx, _, hlt⟩
    · exact .tail hax (.left _ _ hstep)
    · have := ih hne rfl
      refine .tail this (.right _ ?_)
      change m + k < nx + k
      change m < nx at hlt
      omega

/-- Allocating stuttering credits after a source update that changes the thread `j` (Rocq:
`step_inv_alloc`, where the new expressions of the thread are given by `f`). -/
theorem step_inv_alloc (k : Nat) (E : CoPset) (j : Nat) (e₁ : Exp) {X : Type _} (f : X → Exp)
    (Q : X → IProp GF) (hne : ∀ x, f x ≠ e₁) :
    (tpoolPointsTo j e₁ -∗ srcUpd E iprop(∃ x, tpoolPointsTo j (f x) ∗ Q x)) ⊢
      tpoolPointsTo j e₁ -∗ srcUpd E iprop((∃ x, tpoolPointsTo j (f x) ∗ Q x) ∗ stutter k) := by
  unfold srcUpd srcUpdate refSrc
  delta lexSource heapLangSource natSource
  dsimp only
  unfold cfgInterp tpoolPointsTo stutter srcA srcF
  iintro Hupd Hj %⟨⟨tp, σ⟩, n⟩ ⟨⟨Htp, Hh, Htr⟩, Hn⟩
  icases ghost_map_lookup $$ Htp Hj with %h₁
  ihave H := Hupd $$ Hj
  imod H $$ %((tp, σ), n) [Htp Hh Htr Hn] with ⟨%⟨⟨tp', σ'⟩, m⟩, %hsteps, ⟨⟨Htp, Hh, Htr⟩, Hm⟩, %x, Hj, HQ⟩
  · iframe
  icases ghost_map_lookup $$ Htp Hj with %h₂
  have hlu : ((⟨m⟩ : NatC SI), (UCMRA.unit : NatC SI)) ~l~> (⟨m + k⟩, ⟨k⟩) :=
    (local_update_unital_discrete _ _ _ _).mpr fun z _ hz =>
      ⟨trivial, NatC.ext (by
        have := congrArg NatC.n hz
        have hu : (UCMRA.unit : NatC SI).n = 0 := rfl
        simp only [NatC.op_n] at this ⊢; omega)⟩
  imod iOwn_update (ULift.update (Auth.auth_update_alloc hlu)) $$ Hm with Hm
  icases (iOwn_op (E := N.elem)).mp $$ Hm with ⟨Hm, Hk⟩
  imodintro
  iexists ((tp', σ'), m + k)
  isplitr
  · ipureintro
    refine add_stutter (GF := GF) k hsteps fun heq => hne x ?_
    have : tp = tp' := congrArg Prod.fst heq
    subst this
    rw [toMap_get?] at h₁ h₂
    exact Option.some.inj (h₂.symm.trans h₁)
  iframe

/-- Recording the current source configuration (Rocq: `src_log`). -/
theorem src_log (E : CoPset) (j : Nat) (e : Exp) :
    tpoolPointsTo (GF := GF) j e ⊢ weakSrcUpd E iprop(tpoolPointsTo j e ∗
      ∃ (tp : List Exp) (σ : State) (i : Nat), ⌜tp[j]? = some e⌝ ∗ traceIdx i (tp, σ)) := by
  unfold weakSrcUpd weakSrcUpdate refSrc
  delta lexSource heapLangSource natSource
  dsimp only
  unfold cfgInterp tpoolPointsTo
  iintro Hj %⟨⟨tp, σ⟩, n⟩ ⟨⟨Htp, Hh, %l, %hrtc, Htr, #Hidx⟩, Hn⟩
  icases ghost_map_lookup $$ Htp Hj with %h
  rw [toMap_get?] at h
  imodintro
  iexists ((tp, σ), n)
  isplitr
  · ipureintro; exact .refl
  iframe
  isplitr
  · isplitr
    · ipureintro; exact hrtc
    iexact Hidx
  iexists tp, σ, l.length
  isplitr
  · ipureintro; exact h
  iexact Hidx

/-- The configurations recorded by `traceIdx` are reachable in the source (Rocq:
`src_get_trace'`). -/
theorem src_get_trace' (j : Nat) (e : Exp) (i : Nat) (c : Cfg) (a : Cfg × Nat) :
    ⊢ tpoolPointsTo (GF := GF) j e -∗ traceIdx i c -∗ (refSrc (GF := GF)).interp a -∗
      tpoolPointsTo j e ∗ (refSrc (GF := GF)).interp a ∗
        ∃ (tp : List Exp) (σ : State), ⌜tp[j]? = some e ∧
          FromMathlib.Relation.ReflTransGen ErasedStep c (tp, σ)⌝ := by
  obtain ⟨⟨tp, σ⟩, n⟩ := a
  unfold refSrc
  delta lexSource heapLangSource natSource
  dsimp only
  unfold cfgInterp tpoolPointsTo traceIdx
  iintro Hj #Hi ⟨⟨Htp, Hh, %l, %hrtc, Htr, #Hidx⟩, Hn⟩
  icases ghost_map_lookup $$ Htp Hj with %h
  icases ghost_map_lookup $$ Htr Hi with %hi
  rw [toMap_get?] at h hi
  iframe
  isplitr
  · isplitr
    · ipureintro; exact hrtc
    iexact Hidx
  iexists tp, σ
  ipureintro
  exact ⟨h, RtcList.lookup_rtc hi hrtc⟩

/-- Rocq: `src_get_trace`. -/
theorem src_get_trace (E : CoPset) (j : Nat) (e : Exp) (i : Nat) (c : Cfg) :
    tpoolPointsTo (GF := GF) j e ∗ traceIdx i c ⊢ weakSrcUpd E iprop(tpoolPointsTo j e ∗
      ∃ (tp : List Exp) (σ : State), ⌜tp[j]? = some e ∧
        FromMathlib.Relation.ReflTransGen ErasedStep c (tp, σ)⌝) := by
  unfold weakSrcUpd weakSrcUpdate
  iintro ⟨Hj, #Hi⟩ %a Ha
  ihave H := src_get_trace' j e i c a $$ Hj Hi Ha
  icases H with ⟨Hj, Ha, Hex⟩
  imodintro
  iexists a
  isplitr
  · ipureintro; exact .refl
  iframe

end Stuttering

/-! ## Adequacy -/

section Adequacy

open FromMathlib.Relation

/-- The source thread `0` (Rocq: `src e`). -/
abbrev src {GF : BundledGFunctors} [RHeapG GF] (e : Exp) : IProp GF := tpoolPointsTo 0 e

/-- The pre-instances of the ghost state of the refinement logic (Rocq: `rheapPreG`). -/
class RHeapPreS (GF : BundledGFunctors) extends HeapLangTPreS GF where
  tpool : GhostMapG GF Nat Exp NatMap
  heapS : GhostMapG GF Loc SrcVal HeapF
  trace : GhostMapG GF Nat Cfg NatMap

attribute [reducible, instance] RHeapPreS.tpool RHeapPreS.heapS RHeapPreS.trace

theorem lex_rtc_fst {X Y : Type _} {R : X → X → Prop} {S : Y → Y → Prop} {a b : X × Y}
    (h : ReflTransGen (Lex R S) a b) : ReflTransGen R a.1 b.1 := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih =>
    cases hbc with
    | left _ _ hstep => exact .tail ih hstep
    | right _ _ => exact ih

/-- Allocating ghost state with a name chosen by the existential property. -/
theorem satisfiableAt_alloc' {GF : BundledGFunctors} [W : WsatGS GF] {X : Type}
    [SIdxLarge.{0} SI] {P : IProp GF} {Q : X → IProp GF} (h : satisfiableAt ⊤ P)
    (hQ : ⊢ |==> ∃ x, Q x) : ∃ x, satisfiableAt ⊤ iprop(P ∗ Q x) := by
  refine satisfiableAt_exists (satisfiableAt_fupd (E1 := ⊤) (satisfiableAt_mono h ?_))
  iintro HP
  imod hQ with ⟨%x, HQ⟩
  imodintro
  iexists x
  iframe

theorem ghost_map_alloc_single {GF : BundledGFunctors} {K V : Type _} {H : Type _ → Type _}
    [Std.LawfulFiniteMap H K] [DecidableEq K] [GhostMapG GF K V H] (k : K) (v : V) :
    ⊢@{IProp GF} |==> ∃ γ, ghost_map_auth γ (.own 1) (PartialMap.insert (∅ : H V) k v) ∗
      ghost_map_elem γ (.own 1) k v := by
  imod ghost_map_alloc_empty (K := K) (V := V) (H := H) with ⟨%γ, Hγ⟩
  imod ghost_map_insert k v (LawfulPartialMap.get?_empty _) $$ Hγ with ⟨Hγ, Hk⟩
  imodintro
  iexists γ
  iframe

theorem ghost_map_alloc_single_persist {GF : BundledGFunctors} {K V : Type _}
    {H : Type _ → Type _} [Std.LawfulFiniteMap H K] [DecidableEq K] [GhostMapG GF K V H]
    (k : K) (v : V) :
    ⊢@{IProp GF} |==> ∃ γ, ghost_map_auth γ (.own 1) (PartialMap.insert (∅ : H V) k v) ∗
      ghost_map_elem γ .discard k v := by
  imod ghost_map_alloc_empty (K := K) (V := V) (H := H) with ⟨%γ, Hγ⟩
  imod ghost_map_insert_persist k v (LawfulPartialMap.get?_empty _) $$ Hγ with ⟨Hγ, Hk⟩
  imodintro
  iexists γ
  iframe

theorem toMap_singleton {V : Type _} (x : V) :
    toMap [x] = PartialMap.insert (∅ : NatMap V) 0 x := rfl

/-- Adequacy of the refinement logic (Rocq: `heap_lang_ref_adequacy`): if the target `t` refines
the source `s`, then every result of `t` is related by `φ` to a result of `s`, and `t` is strongly
normalizing if `s` is. The name of the `NatSourceG` instance is ignored (only its ghost-state
embedding is used). -/
theorem heap_lang_ref_adequacy {GF : BundledGFunctors} [SIdxLarge.{0} SI] [Hpre : RHeapPreS GF]
    [Hna : NaInvG GF] [Enat : NatSourceG GF] (φ : Val → Val → Prop) (s t : Exp) (σ σs : State)
    (Hobj : ∀ [RHeapG GF] [SeqG GF] [NatSourceG GF],
      src s ⊢ seq (src := refSrc (GF := GF)) (ι := heapRefIrisGS) ⊤ t
        fun v => iprop(∃ v' : Val, src v' ∗ ⌜φ v v'⌝)) :
    (∀ (ts : List Exp) (σ' : State) (v : Val),
      ReflTransGen ErasedStep ([t], σ) ((v : Exp) :: ts, σ') →
      ∃ (v' : Val) (σs' : State) (ts' : List Exp),
        ReflTransGen ErasedStep ([s], σs) ((v' : Exp) :: ts', σs') ∧ φ v v') ∧
    (StronglyNormalizing ErasedStep ([s], σs) → StronglyNormalizing ErasedStep ([t], σ)) := by
  -- allocate world satisfaction
  have h0 : UPred.satisfiable iprop(∃ γ γe γd : GName,
      wsat (W := WsatGS.ofNames (GF := GF) γ γe γd) ∗
        ownE (W := WsatGS.ofNames (GF := GF) γ γe γd) ⊤) :=
    UPred.satisfiable_bupd (UPred.satisfiable_intro (true_emp.mp.trans wsat_alloc_names))
  obtain ⟨γ, h0⟩ := UPred.satisfiable_exists h0
  obtain ⟨γe, h0⟩ := UPred.satisfiable_exists h0
  obtain ⟨γd, h0⟩ := UPred.satisfiable_exists h0
  letI W : WsatGS GF := WsatGS.ofNames γ γe γd
  have h1 : satisfiableAt ⊤ iprop(True) :=
    UPred.satisfiable_mono h0 (sep_mono_right sep_emp.mpr |>.trans
      (sep_mono_right (sep_mono_right true_intro)))
  -- the target heap
  obtain ⟨γh, h2⟩ := satisfiableAt_alloc' h1 (genHeap_init_names (L := Loc) (V := Option Val)
    (H := HeapF) (GF := GF) σ.heap)
  obtain ⟨γm, h2⟩ := satisfiableAt_exists (P := fun γm : GName =>
      genHeapInterp (G := (⟨γh, γm⟩ : genHeapGS Loc (Option Val) GF HeapF)) σ.heap)
    (satisfiableAt_mono h2 (by
      iintro ⟨-, %γm, Hh, -, -⟩
      iexists γm
      iexact Hh))
  letI G : genHeapGS Loc (Option Val) GF HeapF := ⟨γh, γm⟩
  -- the source thread pool, heap and trace
  obtain ⟨γtp, h3⟩ := satisfiableAt_alloc' h2
    (ghost_map_alloc_single (GF := GF) (H := NatMap) (V := Exp) 0 s)
  obtain ⟨γhs, h4⟩ := satisfiableAt_alloc' h3
    (ghost_map_alloc (GF := GF) (K := Loc) (H := HeapF) (srcHeap σs.heap))
  obtain ⟨γtr, h5⟩ := satisfiableAt_alloc' h4
    (ghost_map_alloc_single_persist (GF := GF) (H := NatMap) (V := Cfg) 0 ([s], σs))
  letI Hr : RHeapG GF := {
    toWsatGS := W, heap := G, proph := ⟨0⟩,
    tpool := Hpre.tpool, tpoolName := γtp,
    heapS := Hpre.heapS, heapSName := γhs,
    trace := Hpre.trace, traceName := γtr }
  -- the pool of non-atomic invariants and the stuttering credits
  obtain ⟨p, h6⟩ := satisfiableAt_alloc' h5 (NonAtomicInvariant.alloc (GF := GF))
  letI Hs : SeqG GF := { toNaInvG := Hna, name := p }
  obtain ⟨γn, h7⟩ := satisfiableAt_alloc' h6 (iOwn_alloc (E := Enat.elem)
    (ULift.up (● (⟨0⟩ : NatC SI))) (Auth.auth_valid.mpr trivial))
  letI Hn : NatSourceG GF := { elem := Enat.elem, name := γn }
  have hsat : satisfiableAt ⊤ iprop((refSrc (GF := GF)).interp (([s], σs), 0) ∗
      heapRefIrisGS.refStateInterp σ 0 ∗
      rwp (src := refSrc (GF := GF)) (ι := heapRefIrisGS) .NotStuck ⊤ t fun v =>
        iprop(NonAtomicInvariant.own Hs.name ⊤ ∗ ∃ v' : Val, src v' ∗ ⌜φ v v'⌝)) := by
    refine satisfiableAt_mono h7 ?_
    have Hobj' := @Hobj Hr Hs Hn
    unfold seq at Hobj'
    iintro ⟨⟨⟨⟨⟨Hh, Htp, Hs0⟩, Hhs, -⟩, Htr, #Hidx⟩, Hna⟩, Hn0⟩
    ihave Hwp := Hobj' $$ [Hs0] Hna
    · unfold src tpoolPointsTo
      iexact Hs0
    iframe Hwp
    delta refSrc lexSource heapLangSource natSource
    dsimp only
    unfold cfgInterp
    rw [refStateInterp_eq]
    dsimp only
    unfold srcA
    rw [toMap_singleton]
    iframe
    iexists []
    rw [List.nil_append, toMap_singleton]
    iframe
    isplitr
    · ipureintro; exact .once _
    unfold traceIdx
    iexact Hidx
  refine ⟨fun ts σ' v hsteps => ?_, fun hsn => ?_⟩
  · obtain ⟨⟨⟨tps, σs'⟩, m⟩, n, hrtc, hsat'⟩ := rwp_result (src := refSrc (GF := GF)) hsteps hsat
    refine satisfiableAt_pure (satisfiableAt_mono hsat' ?_)
    delta refSrc lexSource heapLangSource natSource
    dsimp only
    unfold cfgInterp src tpoolPointsTo
    iintro ⟨⟨⟨Htp, -⟩, -⟩, -, -, %v', Hv', %hφ⟩
    icases ghost_map_lookup $$ Htp Hv' with %hl
    rw [toMap_get?] at hl
    ipureintro
    have hrtc' := lex_rtc_fst hrtc
    cases tps with
    | nil => simp at hl
    | cons e ts' =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
      subst hl
      exact ⟨v', σs', ts', hrtc', hφ⟩
  · refine rwp_sn_preservation (src := refSrc (GF := GF)) ?_ hsat
    exact sn_lex _ _ _ _ hsn fun y => Nat.lt_wfRel.wf.apply y

end Adequacy

end Iris.Transfinite.Refinement
