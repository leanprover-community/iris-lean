/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Iris.HeapLang.PrimitiveLaws

/-! # Derived HeapLang laws

This file extends the HeapLang program logic with some derived laws (not using the lifting
lemmas) about arrays and prophecies.

Iris-Lean has no total weakest precondition yet, so only the partial (`wp_`) versions of the
laws are ported.

For utility functions on arrays (e.g. freeing/copying an array), see `Iris.HeapLang.Lib.Array`. -/

@[expose] public section
namespace Iris.HeapLang

open Iris BI ProofMode ProgramLogic Std

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
variable {l : Loc} {dq : DFrac} {v : Val} {vs : List Val}

/-! ## The `array` connective

`array` is a version of `pointsTo` that works with lists of values. -/

@[rocq_alias heap_lang.array]
def array (l : Loc) (dq : DFrac) (vs : List Val) : IProp GF :=
  iprop([∗list] i ↦ v ∈ vs, (l + Int.ofNat i) ↦{dq} some v)

@[inherit_doc array] notation:50 l:50 " ↦∗{" dq "} " vs:50 => array l dq vs
@[inherit_doc array] notation:50 l:50 " ↦∗ " vs:50 => array l (DFrac.own 1) vs

@[rocq_alias heap_lang.array_timeless]
instance instTimelessArray : Timeless (l ↦∗{dq} vs : IProp GF) := by
  unfold array; infer_instance

@[rocq_alias heap_lang.array_fractional]
instance instFractionalArray : Fractional (fun q => (l ↦∗{.own q} vs : IProp GF)) := by
  unfold array; infer_instance

@[rocq_alias heap_lang.array_as_fractional]
instance instAsFractionalArray {q : Qp} :
    AsFractional (l ↦∗{.own q} vs : IProp GF) ioΦ (l ↦∗{.own ·} vs) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := instFractionalArray

@[rocq_alias heap_lang.array_nil]
theorem array_nil : (l ↦∗{dq} [] : IProp GF) ⊣⊢ emp := .rfl

@[rocq_alias heap_lang.array_singleton]
theorem array_singleton : (l ↦∗{dq} [v] : IProp GF) ⊣⊢ l ↦{dq} some v := by
  unfold array
  refine BigSepL.bigSepL_singleton.trans (.of_eq ?_)
  rw [show l + Int.ofNat 0 = l from loc_add_zero l]

@[rocq_alias heap_lang.array_app]
theorem array_app {ws : List Val} :
    (l ↦∗{dq} (vs ++ ws) : IProp GF) ⊣⊢ l ↦∗{dq} vs ∗ (l + Int.ofNat vs.length) ↦∗{dq} ws := by
  unfold array
  refine BigSepL.bigSepL_append.trans
    (sep_congr_right (.of_eq (BigSepL.bigSepL_eq_of_forall_eq ?_)))
  intro k x
  congr 1
  ext
  simp
  omega

@[rocq_alias heap_lang.array_cons]
theorem array_cons :
    (l ↦∗{dq} (v :: vs) : IProp GF) ⊣⊢ l ↦{dq} some v ∗ (l + (1 : Int)) ↦∗{dq} vs := by
  unfold array
  refine BigSepL.bigSepL_cons.trans
    (sep_congr (.of_eq ?_) (.of_eq (BigSepL.bigSepL_eq_of_forall_eq ?_)))
  · rw [show l + Int.ofNat 0 = l from loc_add_zero l]
  · intro k x
    congr 1
    ext
    simp
    omega

@[rocq_alias heap_lang.array_cons_frame]
instance (priority := high) frameArrayCons {R Q : IProp GF}
    [h : Frame false R iprop(l ↦{dq} some v ∗ (l + (1 : Int)) ↦∗{dq} vs) Q] :
    Frame false R (l ↦∗{dq} (v :: vs)) Q where
  frame := h.frame.trans array_cons.2

@[rocq_alias heap_lang.update_array]
theorem update_array {off : Nat} (h : vs[off]? = some v) :
    (l ↦∗{dq} vs : IProp GF) ⊢ (l + Int.ofNat off) ↦{dq} some v ∗
      ∀ v', (l + Int.ofNat off) ↦{dq} some v' -∗ l ↦∗{dq} vs.set off v' :=
  BigSepL.bigSepL_insert_acc h

/-- The array `vs` is unchanged when the element read out of it is written back. -/
private theorem set_getElem?_self {off : Nat} (h : vs[off]? = some v) : vs.set off v = vs := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.set_getElem_self hlt

/-- `update_array` specialised to a read: the array is restored unchanged. -/
private theorem update_array_read {off : Nat} (h : vs[off]? = some v) :
    (l ↦∗{dq} vs : IProp GF) ⊢ (l + Int.ofNat off) ↦{dq} some v ∗
      ((l + Int.ofNat off) ↦{dq} some v -∗ l ↦∗{dq} vs) :=
  (update_array h).trans <| sep_mono_right <| (forall_elim v).trans <|
    wand_mono .rfl (BiEntails.of_eq (congrArg (array l dq) (set_getElem?_self h))).1

/-- Recast a primitive law whose postcondition pins the returned value into continuation-passing
form, framing the continuation across the step. -/
private theorem wp_cps_of_pure_post {e : Exp} {P P' : IProp GF} {r : Val}
    (hval : toVal e = none) (hwp : ▷ P ⊢ WP e @ s; E {{ v', ⌜v' = r⌝ ∗ P' }}) :
    ▷ P ∗ ▷ (P' -∗ Φ r) ⊢ WP e @ s; E {{ Φ }} := by
  refine (sep_mono hwp .rfl).trans (sep_comm.1.trans ?_)
  refine (wp_frame_step_l' hval LawfulSet.subset_refl).trans (wp_mono fun _ => ?_)
  iintro ⟨Hcont, %hv, HP'⟩
  subst hv
  iapply Hcont $$ HP'

/-! ## Rules for allocation -/

@[rocq_alias heap_lang.pointsto_seq_array]
theorem pointsTo_seq_array {n : Nat} :
    ([∗list] i ∈ List.range n, (l + Int.ofNat i) ↦{dq} some v) ⊢
      (l ↦∗{dq} List.replicate n v : IProp GF) := by
  unfold array
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    rw [List.range_succ, List.replicate_succ']
    refine BigSepL.bigSepL_snoc.1.trans (.trans ?_ BigSepL.bigSepL_snoc.2)
    simp only [List.length_replicate]
    exact sep_mono ih .rfl

@[rocq_alias heap_lang.wp_allocN]
theorem wp_allocN (v : Val) {n : Int} (hn : 0 < n) :
    ▷ (∀ l : Loc, (l ↦∗ List.replicate n.toNat v ∗
        [∗list] i ∈ List.range n.toNat, metaToken (l + Int.ofNat i) ⊤) -∗ Φ (.lit <| .loc l)) -∗
    WP hl(allocn(#n, &v)) @ s; E {{ Φ }} := by
  iintro HΦ
  iapply wp_allocN_seq v hn
  iintro !> %l Hl
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hl with ⟨Hpts, Htok⟩
  iapply HΦ
  iframe Htok
  iapply pointsTo_seq_array $$ Hpts

@[rocq_alias heap_lang.wp_allocN_vec]
theorem wp_allocN_vec (v : Val) {n : Int} (hn : 0 < n) :
    ▷ (∀ l : Loc, (l ↦∗ (Vector.replicate n.toNat v).toList ∗
        [∗list] i ∈ List.range n.toNat, metaToken (l + Int.ofNat i) ⊤) -∗ Φ (.lit <| .loc l)) -∗
    WP hl(allocn(#n, &v)) @ s; E {{ Φ }} :=
  Vector.toList_replicate ▸ wp_allocN v hn

/-! ## Rules for accessing array elements -/

@[rocq_alias heap_lang.wp_load_offset]
theorem wp_load_offset {off : Nat} (h : vs[off]? = some v) :
    ▷ l ↦∗{dq} vs -∗ ▷ ((l ↦∗{dq} vs : IProp GF) -∗ Φ v) -∗
    WP hl(!v(#(l + Int.ofNat off))) @ s; E {{ Φ }} := by
  iintro Hl HΦ
  icases (later_mono (update_array_read h)).trans later_sep.1 $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_load $$ Hpt
  iintro !> Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

@[rocq_alias heap_lang.wp_load_offset_vec]
theorem wp_load_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ▷ l ↦∗{dq} ws.toList -∗ ▷ ((l ↦∗{dq} ws.toList : IProp GF) -∗ Φ ws[off]) -∗
    WP hl(!v(#(l + Int.ofNat off.val))) @ s; E {{ Φ }} :=
  wp_load_offset (by simp)

@[rocq_alias heap_lang.wp_store_offset]
theorem wp_store_offset {off : Nat} {w : Val} (h : vs[off]? = some w) :
    ▷ l ↦∗ vs -∗ ▷ ((l ↦∗ vs.set off v : IProp GF) -∗ Φ hl_val(#())) -∗
    WP hl(v(#(l + Int.ofNat off)) ← &v) @ s; E {{ Φ }} := by
  iintro Hl HΦ
  icases (later_mono (update_array (dq := .own 1) h)).trans later_sep.1 $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_store $$ Hpt
  iintro !> Hpt
  iapply HΦ
  iapply Hclose $$ %v Hpt

@[rocq_alias heap_lang.wp_store_offset_vec]
theorem wp_store_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ▷ l ↦∗ ws.toList -∗ ▷ ((l ↦∗ (ws.set off v).toList : IProp GF) -∗ Φ hl_val(#())) -∗
    WP hl(v(#(l + Int.ofNat off.val)) ← &v) @ s; E {{ Φ }} := by
  rw [Vector.toList_set]
  exact wp_store_offset (w := ws[off]) (by simp)

@[rocq_alias heap_lang.wp_xchg_offset]
theorem wp_xchg_offset {off : Nat} {w : Val} (h : vs[off]? = some v) :
    ▷ l ↦∗ vs -∗ ▷ ((l ↦∗ vs.set off w : IProp GF) -∗ Φ v) -∗
    WP hl(xchg(#(l + Int.ofNat off), &w)) @ s; E {{ Φ }} := by
  iintro Hl HΦ
  icases (later_mono (update_array (dq := .own 1) h)).trans later_sep.1 $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_cps_of_pure_post rfl wp_xchg
  iframe Hpt
  iintro !> Hpt
  iapply HΦ
  iapply Hclose $$ %w Hpt

@[rocq_alias heap_lang.wp_xchg_offset_vec]
theorem wp_xchg_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    ▷ l ↦∗ ws.toList -∗ ▷ ((l ↦∗ (ws.set off v).toList : IProp GF) -∗ Φ ws[off]) -∗
    WP hl(xchg(#(l + Int.ofNat off.val), &v)) @ s; E {{ Φ }} := by
  rw [Vector.toList_set]
  exact wp_xchg_offset (by simp)

@[rocq_alias heap_lang.wp_cmpxchg_suc_offset]
theorem wp_cmpXchg_true_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v)
    (heq : v = v1) (hsafe : v.compareSafe v1) :
    ▷ l ↦∗ vs -∗ ▷ ((l ↦∗ vs.set off v2 : IProp GF) -∗ Φ hl_val((&v, #true))) -∗
    WP hl(cmpXchg(#(l + Int.ofNat off), &v1, &v2)) @ s; E {{ Φ }} := by
  iintro Hl HΦ
  icases (later_mono (update_array (dq := .own 1) h)).trans later_sep.1 $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_cps_of_pure_post rfl (wp_cmpXchg_true rfl rfl hsafe (decide_eq_true heq))
  iframe Hpt
  iintro !> Hpt
  iapply HΦ
  iapply Hclose $$ %v2 Hpt

@[rocq_alias heap_lang.wp_cmpxchg_suc_offset_vec]
theorem wp_cmpXchg_true_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (heq : ws[off] = v1) (hsafe : ws[off].compareSafe v1) :
    ▷ l ↦∗ ws.toList -∗
    ▷ ((l ↦∗ (ws.set off v2).toList : IProp GF) -∗ Φ hl_val((&ws[off], #true))) -∗
    WP hl(cmpXchg(#(l + Int.ofNat off.val), &v1, &v2)) @ s; E {{ Φ }} := by
  rw [Vector.toList_set]
  exact wp_cmpXchg_true_offset (by simp) heq hsafe

@[rocq_alias heap_lang.wp_cmpxchg_fail_offset]
theorem wp_cmpXchg_fail_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v)
    (hne : v ≠ v1) (hsafe : v.compareSafe v1) :
    ▷ l ↦∗{dq} vs -∗ ▷ ((l ↦∗{dq} vs : IProp GF) -∗ Φ hl_val((&v, #false))) -∗
    WP hl(cmpXchg(#(l + Int.ofNat off), &v1, &v2)) @ s; E {{ Φ }} := by
  iintro Hl HΦ
  icases (later_mono (update_array_read h)).trans later_sep.1 $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_cps_of_pure_post rfl (wp_cmpXchg_fail rfl rfl hsafe (decide_eq_false hne))
  iframe Hpt
  iintro !> Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

@[rocq_alias heap_lang.wp_cmpxchg_fail_offset_vec]
theorem wp_cmpXchg_fail_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (hne : ws[off] ≠ v1) (hsafe : ws[off].compareSafe v1) :
    ▷ l ↦∗{dq} ws.toList -∗
    ▷ ((l ↦∗{dq} ws.toList : IProp GF) -∗ Φ hl_val((&ws[off], #false))) -∗
    WP hl(cmpXchg(#(l + Int.ofNat off.val), &v1, &v2)) @ s; E {{ Φ }} :=
  wp_cmpXchg_fail_offset (by simp) hne hsafe

@[rocq_alias heap_lang.wp_faa_offset]
theorem wp_faa_offset {off : Nat} {i1 i2 : Int} (h : vs[off]? = some hl_val(#i1)) :
    ▷ l ↦∗ vs -∗
    ▷ ((l ↦∗ vs.set off hl_val(#(i1 + i2)) : IProp GF) -∗ Φ hl_val(#i1)) -∗
    WP hl(faa(#(l + Int.ofNat off), #i2)) @ s; E {{ Φ }} := by
  iintro Hl HΦ
  icases (later_mono (update_array (dq := .own 1) h)).trans later_sep.1 $$ Hl with ⟨Hpt, Hclose⟩
  iapply wp_cps_of_pure_post rfl wp_faa
  iframe Hpt
  iintro !> Hpt
  iapply HΦ
  iapply Hclose $$ %hl_val(#(i1 + i2)) Hpt

@[rocq_alias heap_lang.wp_faa_offset_vec]
theorem wp_faa_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {i1 i2 : Int}
    (h : ws[off] = hl_val(#i1)) :
    ▷ l ↦∗ ws.toList -∗
    ▷ ((l ↦∗ (ws.set off hl_val(#(i1 + i2))).toList : IProp GF) -∗ Φ hl_val(#i1)) -∗
    WP hl(faa(#(l + Int.ofNat off.val), #i2)) @ s; E {{ Φ }} := by
  rw [Vector.toList_set]
  exact wp_faa_offset (by simpa using h)

/-! ## Derived prophecy laws -/

@[rocq_alias heap_lang.wp_resolve_cmpxchg_suc]
theorem wp_resolve_cmpXchg_true {p : ProphId} {pvs : List (Val × Val)} {v1 v2 w : Val}
    (hsafe : v1.compareSafe v1) :
    proph p pvs -∗ ▷ l ↦ some v1 -∗
    ▷ ((∃ pvs', ⌜pvs = (hl_val((&v1, #true)), w) :: pvs'⌝ ∗ proph p pvs' ∗ l ↦ some v2) -∗
      Φ hl_val((&v1, #true))) -∗
    WP hl(resolve(cmpXchg(#l, &v1, &v2), v(#p), v(&w))) @ s; E {{ Φ }} := by
  iintro Hp Hl HΦ
  iapply wp_resolve inferInstance (hne := rfl) $$ Hp
  iapply wp_cps_of_pure_post rfl (wp_cmpXchg_true rfl rfl hsafe (decide_eq_true rfl))
  iframe Hl
  iintro !> Hl %pvs' %heq Hp
  iapply HΦ
  iexists pvs'
  iframe Hp Hl %heq

@[rocq_alias heap_lang.wp_resolve_cmpxchg_fail]
theorem wp_resolve_cmpXchg_fail {p : ProphId} {pvs : List (Val × Val)} {v1 v2 w : Val}
    (hne : v ≠ v1) (hsafe : v.compareSafe v1) :
    proph p pvs -∗ ▷ l ↦{dq} some v -∗
    ▷ ((∃ pvs', ⌜pvs = (hl_val((&v, #false)), w) :: pvs'⌝ ∗ proph p pvs' ∗ l ↦{dq} some v) -∗
      Φ hl_val((&v, #false))) -∗
    WP hl(resolve(cmpXchg(#l, &v1, &v2), v(#p), v(&w))) @ s; E {{ Φ }} := by
  iintro Hp Hl HΦ
  iapply wp_resolve inferInstance (hne := rfl) $$ Hp
  iapply wp_cps_of_pure_post rfl (wp_cmpXchg_fail rfl rfl hsafe (decide_eq_false hne))
  iframe Hl
  iintro !> Hl %pvs' %heq Hp
  iapply HΦ
  iexists pvs'
  iframe Hp Hl %heq

end Iris.HeapLang
