/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import IrisMath.Termination.Derived

/-! # Thunks

This file ports `theories/examples/termination/thunk.v` of Transfinite Iris: specifications of
a memoizing thunk for the transfinite weakest precondition (partial correctness), the time-credit
weakest precondition `tcwp` (termination), and the sequential weakest precondition, where each
call of the thunk costs one time credit (`thunk_sequential_spec`) or the credit is paid
upfront (`thunk_sequential_prepaid_spec`).
-/

@[expose] public noncomputable section

universe w v u

namespace Iris.Transfinite.Termination

open Iris Iris.Std Iris.BI Iris.HeapLang Iris.HeapLang.Transfinite ProgramLogic Language

variable {SI : Type v} [instSI : Iris.SIdx SI]
local stepindex SI

/-- A memoizing thunk (Rocq: `thunk`). -/
def thunk : Val := hl_val%
  λ f, let r := ref(none());
    λ _, match !r with
      | some(v) => v
      | none() => (let y := f #(); r ← some(y); y)

variable {GF : BundledGFunctors.{u}} [Hheap : HeapLangTGS GF]

/-- Rocq: `thunk_partial_spec`. -/
theorem thunk_partial_spec (f : Val) (Φ : Val → IProp GF) :
    ⊢ Iris.Transfinite.wp .NotStuck ⊤ hl(v(&f) #()) Φ -∗
      Iris.Transfinite.wp .NotStuck ⊤ hl(v(&thunk) v(&f))
        (fun g => Iris.Transfinite.wp .NotStuck ⊤ hl(v(&g) #()) Φ) := by
  iintro Hf
  unfold thunk
  twp_pures
  twp_apply wp_alloc
  iintro %r Hr
  twp_pures
  twp_apply wp_load $$ Hr
  iintro Hr
  twp_pures
  twp_apply wp_wand $$ Hf
  iintro %v Hv
  twp_pures
  twp_apply wp_store $$ Hr
  iintro Hr
  twp_pures
  iexact Hv

variable [Htc : TcGS.{w} GF]

/-- Rocq: `thunk_spec`. -/
theorem thunk_spec (f : Val) (Φ : Val → IProp GF) :
    ⊢ tcwp (ι := heapRefIrisGS) (G := Htc) .NotStuck ⊤ hl(v(&f) #()) Φ -∗
      tcwp (ι := heapRefIrisGS) (G := Htc) .NotStuck ⊤ hl(v(&thunk) v(&f))
        (fun g => tcwp (ι := heapRefIrisGS) (G := Htc) .NotStuck ⊤ hl(v(&g) #()) Φ) := by
  iintro Hf
  unfold thunk
  twp_pures
  twp_apply rwp_alloc
  iintro %r Hr
  twp_pures
  twp_apply rwp_load $$ Hr
  iintro Hr
  twp_pures
  twp_apply rwp_wand $$ Hf
  iintro %v Hv
  twp_pures
  twp_apply rwp_store $$ Hr
  iintro Hr
  twp_pures
  iexact Hv

variable [Hseq : SeqG GF] (N : Namespace)

/-- The invariant of the thunk (Rocq: `thunk_inv`). -/
def thunkInv (r : Loc) (f : Val) (Φ : Val → IProp GF) : IProp GF :=
  iprop((r ↦ some hl_val(none()) ∗ tseq.{w} (⊤ \ ↑N) hl(v(&f) #()) Φ) ∨
    (∃ v, r ↦ some hl_val(some(&v)) ∗ Φ v))

theorem nclose_subset_top : (↑N : CoPset) ⊆ ⊤ := fun _ _ => CoPset.mem_full

/-- Rocq: `thunk_sequential_spec`. Every call of the thunk costs one time credit. -/
theorem thunk_sequential_spec (f : Val) (Φ : Val → IProp GF) [∀ x, Persistent (Φ x)] :
    ⊢ tseq.{w} (⊤ \ ↑N) hl(v(&f) #()) Φ -∗
      tseq.{w} ⊤ hl(v(&thunk) v(&f))
        (fun g => iprop(□ (tc (GF := GF) 1 -∗ tseq.{w} ⊤ hl(v(&g) #()) Φ))) := by
  iintro Hf
  unfold tseq seq
  iintro Hna
  unfold thunk
  twp_pures
  twp_apply rwp_alloc
  iintro %r Hr
  dsimp only
  ihave HI : ▷ thunkInv.{w} N r f Φ $$ [Hr Hf]
  · inext
    unfold thunkInv tseq seq
    ileft
    iframe
  imod NonAtomicInvariant.inv_alloc (p := Hseq.name) (N := N) $$ HI with #I
  twp_pures
  iframe Hna
  iintro !> Hc Hna
  twp_pures
  twp_bind (!_)
  imod NonAtomicInvariant.inv_acc_open (nclose_subset_top N) (nclose_subset_top N) $$ I Hna
    with P
  iapply tcwp_burn_credit rfl $$ Hc
  inext
  icases P with ⟨HP, Hna, Hclose⟩
  unfold thunkInv
  icases HP with (⟨Hr, Hwp⟩ | ⟨%v, Hr, #HΦ⟩)
  · twp_apply rswp_load $$ Hr
    iintro Hr
    twp_pures
    unfold tseq seq
    ihave Hwp := Hwp $$ Hna
    twp_apply rwp_wand $$ Hwp
    iintro %v ⟨Hna, #HΦ⟩
    twp_pures
    twp_apply rwp_store $$ Hr
    iintro Hr
    imod Hclose $$ [Hr Hna] with Hna
    · iframe Hna
      inext
      iright
      iexists v
      iframe Hr HΦ
    twp_pures
    iframe Hna HΦ
  · twp_apply rswp_load $$ Hr
    iintro Hr
    imod Hclose $$ [Hr Hna] with Hna
    · iframe Hna
      inext
      iright
      iexists v
      iframe Hr HΦ
    twp_pures
    iframe Hna HΦ

/-! ## Prepaid thunks -/

section Prepaid

variable [Htok : ElemG GF (constOFU.{max u v} (Auth Unit))]

/-- The timeless part of the invariant of a prepaid thunk (Rocq: `prepaid_inv_tl`). -/
def prepaidTl (γ : GName) (r : Loc) (Φ : Val → IProp GF) : IProp GF :=
  iprop((r ↦ some hl_val(none()) ∗ tc (GF := GF) (1 : Ordinal.{w}) ∗
      iOwn (E := Htok) γ (ULift.up (● ()))) ∨
    (∃ v, r ↦ some hl_val(some(&v)) ∗ Φ v))

instance prepaidTl_timeless (γ : GName) (r : Loc) (Φ : Val → IProp GF) [∀ v, Timeless (Φ v)] :
    Timeless (prepaidTl.{w} γ r Φ) := by
  unfold prepaidTl
  haveI h₁ : Timeless iprop(tc (GF := GF) (1 : Ordinal.{w}) ∗
      iOwn (E := Htok) γ (ULift.up (● ()))) :=
    @UPred.sep_timeless' _ _ _ _ _ _ inferInstance inferInstance
  haveI h₂ : Timeless iprop(r ↦ some hl_val(none()) ∗ tc (GF := GF) (1 : Ordinal.{w}) ∗
      iOwn (E := Htok) γ (ULift.up (● ()))) :=
    @UPred.sep_timeless' _ _ _ _ _ _ inferInstance h₁
  haveI h₃ : Timeless iprop(∃ v, r ↦ some hl_val(some(&v)) ∗ Φ v) :=
    @UPred.exists_timeless' _ _ _ _ _ _ (fun _ =>
      @UPred.sep_timeless' _ _ _ _ _ _ inferInstance inferInstance)
  infer_instance

/-- The remaining part of the invariant of a prepaid thunk (Rocq: `prepaid_inv_re`). -/
def prepaidRe (γ : GName) (f : Val) (Φ : Val → IProp GF) : IProp GF :=
  iprop(tseq.{w} ((⊤ \ ↑(N.@"tl")) \ ↑(N.@"re")) hl(v(&f) #()) Φ ∨
    iOwn (E := Htok) γ (ULift.up (● ())))

theorem subset_diff_of_disjoint {E F G : CoPset} (h₁ : E ⊆ F) (h₂ : E ## G) : E ⊆ F \ G :=
  fun _ hp => LawfulSet.mem_diff.mpr ⟨h₁ _ hp, fun hg => h₂ _ ⟨hp, hg⟩⟩

/-- Rocq: `thunk_sequential_prepaid_spec`. The time credit for the evaluation of `f` is paid
when the thunk is created. -/
theorem thunk_sequential_prepaid_spec (f : Val) (Φ : Val → IProp GF) [∀ x, Persistent (Φ x)]
    [∀ x, Timeless (Φ x)] :
    ⊢ tseq.{w} ((⊤ \ ↑(N.@"tl")) \ ↑(N.@"re")) hl(v(&f) #()) Φ -∗ tc (GF := GF) 1 -∗
      tseq.{w} ⊤ hl(v(&thunk) v(&f))
        (fun g => iprop(□ tseq.{w} ⊤ hl(v(&g) #()) Φ)) := by
  iintro Hf Hone
  unfold tseq seq
  iintro Hna
  unfold thunk
  twp_pures
  iapply fupd_rwp
  imod iOwn_alloc (E := Htok) (ULift.up (● ())) (Auth.auth_valid.mpr trivial) with ⟨%γ, Hγ⟩
  imodintro
  twp_apply rwp_alloc
  iintro %r Hr
  dsimp only
  ihave HItl : ▷ prepaidTl.{w} γ r Φ $$ [Hr Hone Hγ]
  · inext
    unfold prepaidTl
    ileft
    iframe
  imod NonAtomicInvariant.inv_alloc (p := Hseq.name) (N := N.@"tl") $$ HItl with #Itl
  ihave HIre : ▷ prepaidRe.{w} N γ f Φ $$ [Hf]
  · inext
    unfold prepaidRe tseq seq
    ileft
    iexact Hf
  imod NonAtomicInvariant.inv_alloc (p := Hseq.name) (N := N.@"re") $$ HIre with #Ire
  twp_pures
  iframe Hna
  iintro !> Hna
  twp_pures
  twp_bind (!_)
  imod NonAtomicInvariant.inv_acc_open_timeless (nclose_subset_top _) (nclose_subset_top _)
    $$ Itl Hna with ⟨HP, Hna, Hclose⟩
  unfold prepaidTl
  icases HP with (⟨Hr, Hone, Hγ⟩ | ⟨%v, Hr, #HΦ⟩)
  · imod NonAtomicInvariant.inv_acc_open (nclose_subset_top _)
      (subset_diff_of_disjoint (nclose_subset_top _) (ndot_ne_disjoint N (by decide)))
      $$ Ire Hna with P
    iapply tcwp_burn_credit rfl $$ Hone
    inext
    icases P with ⟨Hre, Hna, Hclose'⟩
    twp_apply rswp_load $$ Hr
    iintro Hr
    twp_pures
    unfold prepaidRe
    icases Hre with (Hwp | Hγ')
    · unfold tseq seq
      ihave Hwp := Hwp $$ Hna
      twp_apply rwp_wand $$ Hwp
      iintro %v ⟨Hna, #HΦ⟩
      twp_pures
      twp_apply rwp_store $$ Hr
      iintro Hr
      imod Hclose' $$ [Hna Hγ] with Hna
      · iframe Hna
        inext
        iright
        iexact Hγ
      imod Hclose $$ [Hr Hna] with Hna
      · iframe Hna
        inext
        iright
        iexists v
        iframe Hr HΦ
      twp_pures
      iframe Hna HΦ
    · ihave H := (iOwn_op (E := Htok) (γ := γ) (a1 := ULift.up (● ()))
        (a2 := ULift.up (● ()))).mpr $$ [Hγ Hγ']
      · iframe
      ihave ⟨Hv, -⟩ := iOwn_valid_l $$ H
      icases internalCmraValid_discrete.mp $$ Hv with %Hv
      exact (Auth.auth_op_valid.mp Hv).elim
  · twp_apply rwp_load $$ Hr
    iintro Hr
    imod Hclose $$ [Hr Hna] with Hna
    · iframe Hna
      inext
      iright
      iexists v
      iframe Hr HΦ
    twp_pures
    iframe Hna HΦ

end Prepaid

end Iris.Transfinite.Termination
