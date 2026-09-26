/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.HeapLang.Transfinite

/-! # Derived heap_lang laws in Transfinite Iris

Arrays (Rocq: `l ↦∗ vs`) and the rules for accessing array elements (`*_offset`) and allocating
arrays, for `wp`, `swp`, `rwp` and `rswp` (part of `theories/heap_lang/lifting.v`).
-/

@[expose] public noncomputable section

variable {SI : Type _} [instSI : Iris.SIdx SI]
local stepindex SI

namespace Iris.HeapLang.Transfinite

open Iris Iris.Transfinite ProgramLogic Iris.Std Iris.BI

variable {GF : BundledGFunctors} [H : HeapLangTGS GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF} {k : Nat}
variable {l : Loc} {dq : DFrac} {v : Val} {vs : List Val}
variable {A : Type _} [src : Source GF A]

/-- Ownership of a contiguous array (Rocq: `array`, notation `l ↦∗ vs`). -/
def array (l : Loc) (dq : DFrac) (vs : List Val) : IProp GF :=
  iprop([∗list] i ↦ v ∈ vs, (l + i) ↦{dq} (some v))

theorem bigSepL_timeless {vs : List Val} (Φ : Nat → Val → IProp GF)
    (h : ∀ i v, Timeless (Φ i v)) : Timeless ([∗list] i ↦ v ∈ vs, Φ i v) := by
  induction vs generalizing Φ with
  | nil => exact inferInstanceAs (Timeless (PROP := IProp GF) iprop(emp))
  | cons x xs ih =>
    exact @UPred.sep_timeless' _ _ _ _ (Φ 0 x) _ (h 0 x)
      (ih (fun i v => Φ (i + 1) v) (fun _ _ => h _ _))

instance array_timeless : Timeless (array (GF := GF) l dq vs) :=
  bigSepL_timeless _ (fun _ _ => inferInstance)

theorem update_array {off : Nat} (h : vs[off]? = some v) :
    array (GF := GF) l dq vs ⊢ (l + Int.ofNat off) ↦{dq} some v ∗
      ∀ v', (l + Int.ofNat off) ↦{dq} some v' -∗ array l dq (vs.set off v') :=
  BigSepL.bigSepL_insert_acc h

private theorem set_getElem?_self {off : Nat} (h : vs[off]? = some v) : vs.set off v = vs := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.set_getElem_self hlt

theorem update_array_read {off : Nat} (h : vs[off]? = some v) :
    array (GF := GF) l dq vs ⊢ (l + off) ↦{dq} some v ∗ ((l + off) ↦{dq} some v -∗ array l dq vs) := by
  refine (update_array h).trans ?_
  refine sep_mono_right ?_
  refine (forall_elim v).trans (wand_mono .rfl ?_)
  exact (BiEntails.of_eq (congrArg (array l dq) (set_getElem?_self h))).1

theorem pointsTo_seq_array {n : Nat} :
    ([∗list] i ∈ List.range n, (l + i) ↦{dq} some v) ⊢ array (GF := GF) l dq (List.replicate n v) := by
  unfold array
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    rw [List.range_succ, List.replicate_succ']
    refine BigSepL.bigSepL_snoc.1.trans (.trans ?_ BigSepL.bigSepL_snoc.2)
    simp only [List.length_replicate]
    exact sep_mono ih .rfl

/-- Rocq: `swp_allocN`. -/
theorem swp_allocN {n : Int} (hn : 0 < n) :
    ⊢ (∀ l : Loc, array l (DFrac.own 1) (List.replicate n.toNat v) ∗
        ([∗list] i ∈ List.range n.toNat, metaToken (l + i) ⊤) -∗ Φ hl_val(#(.loc l))) -∗
      swp k s E hl(allocn(#n, &v)) Φ := by
  iintro HΦ
  iapply swp_allocN_seq hn
  iintro %l Hl
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hl with ⟨Hpts, Htok⟩
  iapply HΦ
  iframe Htok
  iapply pointsTo_seq_array $$ Hpts

/-- Rocq: `wp_allocN`. -/
theorem wp_allocN {n : Int} (hn : 0 < n) :
    ⊢ (∀ l : Loc, array l (DFrac.own 1) (List.replicate n.toNat v) ∗
        ([∗list] i ∈ List.range n.toNat, metaToken (l + i) ⊤) -∗ Φ hl_val(#(.loc l))) -∗
      Iris.Transfinite.wp s E hl(allocn(#n, &v)) Φ := by
  iintro HΦ
  iapply wp_allocN_seq hn
  iintro %l Hl
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hl with ⟨Hpts, Htok⟩
  iapply HΦ
  iframe Htok
  iapply pointsTo_seq_array $$ Hpts

/-- Rocq: `rswp_allocN`. -/
theorem rswp_allocN {n : Int} (hn : 0 < n) :
    ⊢ (∀ l : Loc, array l (DFrac.own 1) (List.replicate n.toNat v) ∗
        ([∗list] i ∈ List.range n.toNat, metaToken (l + i) ⊤) -∗ Φ hl_val(#(.loc l))) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(allocn(#n, &v)) Φ := by
  iintro HΦ
  iapply rswp_allocN_seq hn
  iintro %l Hl
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hl with ⟨Hpts, Htok⟩
  iapply HΦ
  iframe Htok
  iapply pointsTo_seq_array $$ Hpts

/-- Rocq: `rwp_allocN`. -/
theorem rwp_allocN {n : Int} (hn : 0 < n) :
    ⊢ (∀ l : Loc, array l (DFrac.own 1) (List.replicate n.toNat v) ∗
        ([∗list] i ∈ List.range n.toNat, metaToken (l + i) ⊤) -∗ Φ hl_val(#(.loc l))) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(allocn(#n, &v)) Φ := by
  iintro HΦ
  iapply rwp_allocN_seq hn
  iintro %l Hl
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hl with ⟨Hpts, Htok⟩
  iapply HΦ
  iframe Htok
  iapply pointsTo_seq_array $$ Hpts

/-- Rocq: `swp_load_offset`. -/
theorem swp_load_offset {off : Nat} (h : vs[off]? = some v) :
    ⊢ ▷ array l dq vs -∗ (array l dq vs -∗ Φ v) -∗ swp k s E hl(!v(#(l + off))) Φ := by
  iintro >Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply swp_load  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

/-- Rocq: `swp_store_offset`. -/
theorem swp_store_offset {off : Nat} {w : Val} (h : vs[off]? = some w) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off v) -∗ Φ hl_val(#())) -∗ swp k s E hl(v(#(l + off)) ← &v) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply swp_store  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `swp_xchg_offset`. -/
theorem swp_xchg_offset {off : Nat} {w : Val} (h : vs[off]? = some v) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off w) -∗ Φ v) -∗ swp k s E hl(xchg(#(l + off), &w)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply swp_xchg  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `swp_cmpXchg_suc_offset`. -/
theorem swp_cmpXchg_suc_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v) (heq : v = v1) (hsafe : v.compareSafe v1) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off v2) -∗ Φ hl_val((&v, #true))) -∗ swp k s E hl(cmpXchg(#(l + off), &v1, &v2)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply swp_cmpXchg_suc heq hsafe $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `swp_cmpXchg_fail_offset`. -/
theorem swp_cmpXchg_fail_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v) (hne : v ≠ v1) (hsafe : v.compareSafe v1) :
    ⊢ ▷ array l dq vs -∗ (array l dq vs -∗ Φ hl_val((&v, #false))) -∗ swp k s E hl(cmpXchg(#(l + off), &v1, &v2)) Φ := by
  iintro >Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply swp_cmpXchg_fail hne hsafe $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

/-- Rocq: `swp_faa_offset`. -/
theorem swp_faa_offset {off : Nat} {i1 i2 : Int} (h : vs[off]? = some hl_val(#i1)) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off hl_val(#(i1 + i2))) -∗ Φ hl_val(#i1)) -∗ swp k s E hl(faa(#(l + off), #i2)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply swp_faa  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `wp_load_offset`. -/
theorem wp_load_offset {off : Nat} (h : vs[off]? = some v) :
    ⊢ ▷ array l dq vs -∗ (array l dq vs -∗ Φ v) -∗ Iris.Transfinite.wp s E hl(!v(#(l + off))) Φ := by
  iintro >Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_load  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

/-- Rocq: `wp_store_offset`. -/
theorem wp_store_offset {off : Nat} {w : Val} (h : vs[off]? = some w) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off v) -∗ Φ hl_val(#())) -∗ Iris.Transfinite.wp s E hl(v(#(l + off)) ← &v) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_store  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `wp_xchg_offset`. -/
theorem wp_xchg_offset {off : Nat} {w : Val} (h : vs[off]? = some v) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off w) -∗ Φ v) -∗ Iris.Transfinite.wp s E hl(xchg(#(l + off), &w)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_xchg  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `wp_cmpXchg_suc_offset`. -/
theorem wp_cmpXchg_suc_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v) (heq : v = v1) (hsafe : v.compareSafe v1) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off v2) -∗ Φ hl_val((&v, #true))) -∗ Iris.Transfinite.wp s E hl(cmpXchg(#(l + off), &v1, &v2)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_cmpXchg_suc heq hsafe $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `wp_cmpXchg_fail_offset`. -/
theorem wp_cmpXchg_fail_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v) (hne : v ≠ v1) (hsafe : v.compareSafe v1) :
    ⊢ ▷ array l dq vs -∗ (array l dq vs -∗ Φ hl_val((&v, #false))) -∗ Iris.Transfinite.wp s E hl(cmpXchg(#(l + off), &v1, &v2)) Φ := by
  iintro >Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_cmpXchg_fail hne hsafe $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

/-- Rocq: `wp_faa_offset`. -/
theorem wp_faa_offset {off : Nat} {i1 i2 : Int} (h : vs[off]? = some hl_val(#i1)) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off hl_val(#(i1 + i2))) -∗ Φ hl_val(#i1)) -∗ Iris.Transfinite.wp s E hl(faa(#(l + off), #i2)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_faa  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `rswp_load_offset`. -/
theorem rswp_load_offset {off : Nat} (h : vs[off]? = some v) :
    ⊢ ▷ array l dq vs -∗ (array l dq vs -∗ Φ v) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(!v(#(l + off))) Φ := by
  iintro >Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rswp_load  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

/-- Rocq: `rswp_store_offset`. -/
theorem rswp_store_offset {off : Nat} {w : Val} (h : vs[off]? = some w) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off v) -∗ Φ hl_val(#())) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(v(#(l + off)) ← &v) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rswp_store  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `rswp_xchg_offset`. -/
theorem rswp_xchg_offset {off : Nat} {w : Val} (h : vs[off]? = some v) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off w) -∗ Φ v) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(xchg(#(l + off), &w)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rswp_xchg  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `rswp_cmpXchg_suc_offset`. -/
theorem rswp_cmpXchg_suc_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v) (heq : v = v1) (hsafe : v.compareSafe v1) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off v2) -∗ Φ hl_val((&v, #true))) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(cmpXchg(#(l + off), &v1, &v2)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rswp_cmpXchg_suc heq hsafe $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `rswp_cmpXchg_fail_offset`. -/
theorem rswp_cmpXchg_fail_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v) (hne : v ≠ v1) (hsafe : v.compareSafe v1) :
    ⊢ ▷ array l dq vs -∗ (array l dq vs -∗ Φ hl_val((&v, #false))) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(cmpXchg(#(l + off), &v1, &v2)) Φ := by
  iintro >Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rswp_cmpXchg_fail hne hsafe $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

/-- Rocq: `rswp_faa_offset`. -/
theorem rswp_faa_offset {off : Nat} {i1 i2 : Int} (h : vs[off]? = some hl_val(#i1)) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off hl_val(#(i1 + i2))) -∗ Φ hl_val(#i1)) -∗ rswp (src := src) (ι := heapRefIrisGS) k s E hl(faa(#(l + off), #i2)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rswp_faa  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `rwp_load_offset`. -/
theorem rwp_load_offset {off : Nat} (h : vs[off]? = some v) :
    ⊢ ▷ array l dq vs -∗ (array l dq vs -∗ Φ v) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(!v(#(l + off))) Φ := by
  iintro >Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rwp_load  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

/-- Rocq: `rwp_store_offset`. -/
theorem rwp_store_offset {off : Nat} {w : Val} (h : vs[off]? = some w) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off v) -∗ Φ hl_val(#())) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(v(#(l + off)) ← &v) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rwp_store  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `rwp_xchg_offset`. -/
theorem rwp_xchg_offset {off : Nat} {w : Val} (h : vs[off]? = some v) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off w) -∗ Φ v) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(xchg(#(l + off), &w)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rwp_xchg  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `rwp_cmpXchg_suc_offset`. -/
theorem rwp_cmpXchg_suc_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v) (heq : v = v1) (hsafe : v.compareSafe v1) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off v2) -∗ Φ hl_val((&v, #true))) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(cmpXchg(#(l + off), &v1, &v2)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rwp_cmpXchg_suc heq hsafe $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt

/-- Rocq: `rwp_cmpXchg_fail_offset`. -/
theorem rwp_cmpXchg_fail_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v) (hne : v ≠ v1) (hsafe : v.compareSafe v1) :
    ⊢ ▷ array l dq vs -∗ (array l dq vs -∗ Φ hl_val((&v, #false))) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(cmpXchg(#(l + off), &v1, &v2)) Φ := by
  iintro >Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rwp_cmpXchg_fail hne hsafe $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

/-- Rocq: `rwp_faa_offset`. -/
theorem rwp_faa_offset {off : Nat} {i1 i2 : Int} (h : vs[off]? = some hl_val(#i1)) :
    ⊢ ▷ array l (DFrac.own 1) vs -∗ (array l (DFrac.own 1) (vs.set off hl_val(#(i1 + i2))) -∗ Φ hl_val(#i1)) -∗ rwp (src := src) (ι := heapRefIrisGS) s E hl(faa(#(l + off), #i2)) Φ := by
  iintro >Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply rwp_faa  $$ [Hpt]
  · inext
    iexact Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %_ Hpt


theorem swp_load_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ⊢ ▷ array l dq ws.toList -∗ (array l dq ws.toList -∗ Φ ws[off]) -∗
      swp k s E hl(!v(#(l + off.val))) Φ :=
  swp_load_offset (by simp)

theorem swp_store_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val v) -∗ Φ hl_val(#())) -∗
      swp k s E hl(v(#(l + off.val)) ← &v) Φ :=
  swp_store_offset (w := ws[off]) (by simp)

theorem swp_xchg_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {w : Val} :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val w) -∗ Φ ws[off]) -∗
      swp k s E hl(xchg(#(l + off.val), &w)) Φ :=
  swp_xchg_offset (by simp)

theorem swp_cmpXchg_suc_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (heq : ws[off] = v1) (hsafe : ws[off].compareSafe v1) :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val v2) -∗ Φ hl_val((&ws[off], #true))) -∗
      swp k s E hl(cmpXchg(#(l + off.val), &v1, &v2)) Φ :=
  swp_cmpXchg_suc_offset (by simp) heq hsafe

theorem swp_cmpXchg_fail_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (hne : ws[off] ≠ v1) (hsafe : ws[off].compareSafe v1) :
    ⊢ ▷ array l dq ws.toList -∗
      (array l dq ws.toList -∗ Φ hl_val((&ws[off], #false))) -∗
      swp k s E hl(cmpXchg(#(l + off.val), &v1, &v2)) Φ :=
  swp_cmpXchg_fail_offset (by simp) hne hsafe

theorem swp_faa_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {i1 i2 : Int}
    (h : ws[off] = hl_val(#i1)) :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val hl_val(#(i1 + i2))) -∗ Φ hl_val(#i1)) -∗
      swp k s E hl(faa(#(l + off.val), #i2)) Φ :=
  swp_faa_offset (by simp; first | exact h | simpa using h)

theorem wp_load_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ⊢ ▷ array l dq ws.toList -∗ (array l dq ws.toList -∗ Φ ws[off]) -∗
      Iris.Transfinite.wp s E hl(!v(#(l + off.val))) Φ :=
  wp_load_offset (by simp)

theorem wp_store_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val v) -∗ Φ hl_val(#())) -∗
      Iris.Transfinite.wp s E hl(v(#(l + off.val)) ← &v) Φ :=
  wp_store_offset (w := ws[off]) (by simp)

theorem wp_xchg_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {w : Val} :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val w) -∗ Φ ws[off]) -∗
      Iris.Transfinite.wp s E hl(xchg(#(l + off.val), &w)) Φ :=
  wp_xchg_offset (by simp)

theorem wp_cmpXchg_suc_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (heq : ws[off] = v1) (hsafe : ws[off].compareSafe v1) :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val v2) -∗ Φ hl_val((&ws[off], #true))) -∗
      Iris.Transfinite.wp s E hl(cmpXchg(#(l + off.val), &v1, &v2)) Φ :=
  wp_cmpXchg_suc_offset (by simp) heq hsafe

theorem wp_cmpXchg_fail_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (hne : ws[off] ≠ v1) (hsafe : ws[off].compareSafe v1) :
    ⊢ ▷ array l dq ws.toList -∗
      (array l dq ws.toList -∗ Φ hl_val((&ws[off], #false))) -∗
      Iris.Transfinite.wp s E hl(cmpXchg(#(l + off.val), &v1, &v2)) Φ :=
  wp_cmpXchg_fail_offset (by simp) hne hsafe

theorem wp_faa_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {i1 i2 : Int}
    (h : ws[off] = hl_val(#i1)) :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val hl_val(#(i1 + i2))) -∗ Φ hl_val(#i1)) -∗
      Iris.Transfinite.wp s E hl(faa(#(l + off.val), #i2)) Φ :=
  wp_faa_offset (by simp; first | exact h | simpa using h)

theorem rswp_load_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ⊢ ▷ array l dq ws.toList -∗ (array l dq ws.toList -∗ Φ ws[off]) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(!v(#(l + off.val))) Φ :=
  rswp_load_offset (by simp)

theorem rswp_store_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val v) -∗ Φ hl_val(#())) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(v(#(l + off.val)) ← &v) Φ :=
  rswp_store_offset (w := ws[off]) (by simp)

theorem rswp_xchg_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {w : Val} :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val w) -∗ Φ ws[off]) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(xchg(#(l + off.val), &w)) Φ :=
  rswp_xchg_offset (by simp)

theorem rswp_cmpXchg_suc_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (heq : ws[off] = v1) (hsafe : ws[off].compareSafe v1) :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val v2) -∗ Φ hl_val((&ws[off], #true))) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(cmpXchg(#(l + off.val), &v1, &v2)) Φ :=
  rswp_cmpXchg_suc_offset (by simp) heq hsafe

theorem rswp_cmpXchg_fail_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (hne : ws[off] ≠ v1) (hsafe : ws[off].compareSafe v1) :
    ⊢ ▷ array l dq ws.toList -∗
      (array l dq ws.toList -∗ Φ hl_val((&ws[off], #false))) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(cmpXchg(#(l + off.val), &v1, &v2)) Φ :=
  rswp_cmpXchg_fail_offset (by simp) hne hsafe

theorem rswp_faa_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {i1 i2 : Int}
    (h : ws[off] = hl_val(#i1)) :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val hl_val(#(i1 + i2))) -∗ Φ hl_val(#i1)) -∗
      rswp (src := src) (ι := heapRefIrisGS) k s E hl(faa(#(l + off.val), #i2)) Φ :=
  rswp_faa_offset (by simp; first | exact h | simpa using h)

theorem rwp_load_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ⊢ ▷ array l dq ws.toList -∗ (array l dq ws.toList -∗ Φ ws[off]) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(!v(#(l + off.val))) Φ :=
  rwp_load_offset (by simp)

theorem rwp_store_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val v) -∗ Φ hl_val(#())) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(v(#(l + off.val)) ← &v) Φ :=
  rwp_store_offset (w := ws[off]) (by simp)

theorem rwp_xchg_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {w : Val} :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val w) -∗ Φ ws[off]) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(xchg(#(l + off.val), &w)) Φ :=
  rwp_xchg_offset (by simp)

theorem rwp_cmpXchg_suc_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (heq : ws[off] = v1) (hsafe : ws[off].compareSafe v1) :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val v2) -∗ Φ hl_val((&ws[off], #true))) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(cmpXchg(#(l + off.val), &v1, &v2)) Φ :=
  rwp_cmpXchg_suc_offset (by simp) heq hsafe

theorem rwp_cmpXchg_fail_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (hne : ws[off] ≠ v1) (hsafe : ws[off].compareSafe v1) :
    ⊢ ▷ array l dq ws.toList -∗
      (array l dq ws.toList -∗ Φ hl_val((&ws[off], #false))) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(cmpXchg(#(l + off.val), &v1, &v2)) Φ :=
  rwp_cmpXchg_fail_offset (by simp) hne hsafe

theorem rwp_faa_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {i1 i2 : Int}
    (h : ws[off] = hl_val(#i1)) :
    ⊢ ▷ array l (DFrac.own 1) ws.toList -∗
      (array l (DFrac.own 1) (ws.toList.set off.val hl_val(#(i1 + i2))) -∗ Φ hl_val(#i1)) -∗
      rwp (src := src) (ι := heapRefIrisGS) s E hl(faa(#(l + off.val), #i2)) Φ :=
  rwp_faa_offset (by simp; first | exact h | simpa using h)

end Iris.HeapLang.Transfinite
