/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.HeapLang.PrimitiveLaws

/-! # Derived HeapLang laws -/

@[expose] public section
namespace Iris.HeapLang

open Iris BI ProofMode ProgramLogic Std

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Val → IProp GF}
variable {l : Loc} {dq : DFrac} {v : Val} {vs : List Val}

/-- Predicate for asserting ownership over a contiguous array. -/
@[rocq_alias heap_lang.array]
def array (l : Loc) (dq : DFrac) (vs : List Val) : IProp GF :=
  iprop% [∗list] i ↦ v ∈ vs, (l + i) ↦{dq} (v: Val)

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
  rw [show l + 0 = l from loc_add_zero l]

@[rocq_alias heap_lang.array_app]
theorem array_app {ws : List Val} :
    (l ↦∗{dq} (vs ++ ws) : IProp GF) ⊣⊢ l ↦∗{dq} vs ∗ (l + vs.length) ↦∗{dq} ws := by
  unfold array
  refine BigSepL.bigSepL_append.trans ?_
  refine (sep_congr_right (.of_eq ?_))
  refine BigSepL.bigSepL_eq_of_forall_eq <| @fun k x => ?_
  congr 1; ext
  change l.n + ((k + vs.length : Nat) : Int) = (l.n + (vs.length : Int)) + (k : Int)
  omega

@[rocq_alias heap_lang.array_cons]
theorem array_cons :
    (l ↦∗{dq} (v :: vs) : IProp GF) ⊣⊢ l ↦{dq} some v ∗ (l + (1 : Int)) ↦∗{dq} vs := by
  unfold array
  refine BigSepL.bigSepL_cons.trans ?_
  refine sep_congr (.of_eq ?_) (.of_eq (BigSepL.bigSepL_eq_of_forall_eq @fun k x => ?_))
  · rw [show l + 0 = l from loc_add_zero l]
  · congr 1; ext; change l.n + (k + 1 : Nat) = (l.n + 1) + k; omega

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
    (l ↦∗{dq} vs : IProp GF) ⊢ (l + off) ↦{dq} some v ∗ ((l + off) ↦{dq} some v -∗ l ↦∗{dq} vs) := by
  refine (update_array h).trans ?_
  refine sep_mono_right ?_
  refine (forall_elim v).trans (wand_mono .rfl ?_)
  exact (BiEntails.of_eq (congrArg (array l dq) (set_getElem?_self h))).1

/-! ## Rules for allocation -/

@[rocq_alias heap_lang.pointsto_seq_array]
theorem pointsTo_seq_array {n : Nat} :
    ([∗list] i ∈ List.range n, (l + i) ↦{dq} some v) ⊢ l ↦∗{dq} List.replicate n v := by
  unfold array
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    rw [List.range_succ, List.replicate_succ']
    refine BigSepL.bigSepL_snoc.1.trans (.trans ?_ BigSepL.bigSepL_snoc.2)
    simp only [List.length_replicate]
    exact sep_mono ih .rfl

@[rocq_alias heap_lang.twp_allocN]
theorem twp_allocN (v : Val) {n : Int} (hn : 0 < n) :
    [{ True }] hl(allocn(#n, &v)) @ s; E
    [{ l, RET hl_val(#l); l ↦∗ List.replicate n.toNat v ∗
      [∗list] i ∈ List.range n.toNat, metaToken (l + i) ⊤ }] := by
  iintro %Φ _ HΦ
  iapply twp_allocN_seq hn
  · itrivial
  iintro %l Hl
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hl with ⟨Hpts, Htok⟩
  iapply HΦ
  iframe Htok
  iapply pointsTo_seq_array $$ Hpts

@[rocq_alias heap_lang.wp_allocN]
theorem wp_allocN (v : Val) {n : Int} (hn : 0 < n) :
    {{ True }} hl(allocn(#n, &v)) @ s; E
    {{ l, RET hl_val(#l); l ↦∗ List.replicate n.toNat v ∗
      [∗list] i ∈ List.range n.toNat, metaToken (l + i) ⊤ }} := by
  iintro %Φ _ HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_allocN v hn
  · itrivial
  iintro %l H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_allocN_vec]
theorem twp_allocN_vec (v : Val) {n : Int} (hn : 0 < n) :
    [{ True }] hl(allocn(#n, &v)) @ s; E
    [{ l, RET hl_val(#l); l ↦∗ (Vector.replicate n.toNat v).toList ∗
        [∗list] i ∈ List.range n.toNat, metaToken (l + i) ⊤ }] :=
  Vector.toList_replicate ▸ twp_allocN v hn

@[rocq_alias heap_lang.wp_allocN_vec]
theorem wp_allocN_vec (v : Val) {n : Int} (hn : 0 < n) :
    {{ True }} hl(allocn(#n, &v)) @ s; E
    {{ l, RET hl_val(#l); l ↦∗ (Vector.replicate n.toNat v).toList ∗
        [∗list] i ∈ List.range n.toNat, metaToken (l + i) ⊤ }} := by
  iintro %Φ _ HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_allocN_vec v hn
  · itrivial
  iintro %l H HΦ
  iapply HΦ
  itrivial

/-! ## Rules for accessing array elements -/

@[rocq_alias heap_lang.twp_load_offset]
theorem twp_load_offset {off : Nat} (h : vs[off]? = some v) :
    [{ l ↦∗{dq} vs }] hl(!v(#(l + off))) @ s; E
    [{ RET v; (l ↦∗{dq} vs : IProp GF) }] := by
  iintro %Φ Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply twp_load $$ Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

@[rocq_alias heap_lang.wp_load_offset]
theorem wp_load_offset {off : Nat} (h : vs[off]? = some v) :
    {{ ▷ l ↦∗{dq} vs }} hl(!v(#(l + off))) @ s; E
    {{ RET v; (l ↦∗{dq} vs : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_load_offset h $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_load_offset_vec]
theorem twp_load_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    [{ l ↦∗{dq} ws.toList }] hl(!v(#(l + off.val))) @ s; E
    [{ RET ws[off]; (l ↦∗{dq} ws.toList : IProp GF) }] :=
  twp_load_offset (by simp)

@[rocq_alias heap_lang.wp_load_offset_vec]
theorem wp_load_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    {{ ▷ l ↦∗{dq} ws.toList }} hl(!v(#(l + off.val))) @ s; E
    {{ RET ws[off]; (l ↦∗{dq} ws.toList : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_load_offset_vec $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_store_offset]
theorem twp_store_offset {off : Nat} {w : Val} (h : vs[off]? = some w) :
    [{ l ↦∗ vs }] hl(v(#(l + off)) ← &v) @ s; E
    [{ RET hl_val(#()); (l ↦∗ vs.set off v : IProp GF) }] := by
  iintro %Φ Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply twp_store $$ Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %v Hpt

@[rocq_alias heap_lang.wp_store_offset]
theorem wp_store_offset {off : Nat} {w : Val} (h : vs[off]? = some w) :
    {{ ▷ l ↦∗ vs }} hl(v(#(l + off)) ← &v) @ s; E
    {{ RET hl_val(#()); (l ↦∗ vs.set off v : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_store_offset h $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_store_offset_vec]
theorem twp_store_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    [{ l ↦∗ ws.toList }] hl(v(#(l + Int.ofNat off.val)) ← &v) @ s; E
    [{ RET hl_val(#()); (l ↦∗ (ws.set off v).toList : IProp GF) }] := by
  rw [Vector.toList_set]
  exact twp_store_offset (w := ws[off]) (by simp)

@[rocq_alias heap_lang.wp_store_offset_vec]
theorem wp_store_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    {{ ▷ l ↦∗ ws.toList }} hl(v(#(l + Int.ofNat off.val)) ← &v) @ s; E
    {{ RET hl_val(#()); (l ↦∗ (ws.set off v).toList : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_store_offset_vec $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_xchg_offset]
theorem twp_xchg_offset {off : Nat} {w : Val} (h : vs[off]? = some v) :
    [{ l ↦∗ vs }] hl(xchg(#(l + off), &w)) @ s; E
    [{ RET v; (l ↦∗ vs.set off w : IProp GF) }] := by
  iintro %Φ Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply twp_xchg $$ Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %w Hpt

@[rocq_alias heap_lang.wp_xchg_offset]
theorem wp_xchg_offset {off : Nat} {w : Val} (h : vs[off]? = some v) :
    {{ ▷ l ↦∗ vs }} hl(xchg(#(l + off), &w)) @ s; E
    {{ RET v; (l ↦∗ vs.set off w : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_xchg_offset h $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_xchg_offset_vec]
theorem twp_xchg_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    [{ l ↦∗ ws.toList }] hl(xchg(#(l + off.val), &v)) @ s; E
    [{ RET ws[off]; (l ↦∗ (ws.set off v).toList : IProp GF) }] := by
  rw [Vector.toList_set]
  exact twp_xchg_offset (by simp)

@[rocq_alias heap_lang.wp_xchg_offset_vec]
theorem wp_xchg_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} :
    {{ ▷ l ↦∗ ws.toList }} hl(xchg(#(l + off.val), &v)) @ s; E
    {{ RET ws[off]; (l ↦∗ (ws.set off v).toList : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_xchg_offset_vec $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_cmpxchg_suc_offset]
theorem twp_cmpXchg_true_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v)
    (heq : v = v1) (hsafe : v.compareSafe v1) :
    [{ l ↦∗ vs }] hl(cmpXchg(#(l + off), &v1, &v2)) @ s; E
    [{ RET hl_val((&v, #true)); (l ↦∗ vs.set off v2 : IProp GF) }] := by
  iintro %Φ Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply twp_cmpXchg_true heq hsafe $$ Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %v2 Hpt

@[rocq_alias heap_lang.wp_cmpxchg_suc_offset]
theorem wp_cmpXchg_true_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v)
    (heq : v = v1) (hsafe : v.compareSafe v1) :
    {{ ▷ l ↦∗ vs }} hl(cmpXchg(#(l + off), &v1, &v2)) @ s; E
    {{ RET hl_val((&v, #true)); (l ↦∗ vs.set off v2 : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_cmpXchg_true_offset h heq hsafe $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_cmpxchg_suc_offset_vec]
theorem twp_cmpXchg_true_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (heq : ws[off] = v1) (hsafe : ws[off].compareSafe v1) :
    [{ l ↦∗ ws.toList }] hl(cmpXchg(#(l + off.val), &v1, &v2)) @ s; E
    [{ RET hl_val((&ws[off], #true)); (l ↦∗ (ws.set off v2).toList : IProp GF) }] := by
  rw [Vector.toList_set]
  exact twp_cmpXchg_true_offset (by simp) heq hsafe

@[rocq_alias heap_lang.wp_cmpxchg_suc_offset_vec]
theorem wp_cmpXchg_true_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (heq : ws[off] = v1) (hsafe : ws[off].compareSafe v1) :
    {{ ▷ l ↦∗ ws.toList }} hl(cmpXchg(#(l + off.val), &v1, &v2)) @ s; E
    {{ RET hl_val((&ws[off], #true)); (l ↦∗ (ws.set off v2).toList : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_cmpXchg_true_offset_vec heq hsafe $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_cmpxchg_fail_offset]
theorem twp_cmpXchg_fail_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v)
    (hne : v ≠ v1) (hsafe : v.compareSafe v1) :
    [{ l ↦∗{dq} vs }] hl(cmpXchg(#(l + off), &v1, &v2)) @ s; E
    [{ RET hl_val((&v, #false)); (l ↦∗{dq} vs : IProp GF) }] := by
  iintro %Φ Hl HΦ
  icases update_array_read h $$ Hl with ⟨Hpt, Hclose⟩
  iapply twp_cmpXchg_fail hne hsafe $$ Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ Hpt

@[rocq_alias heap_lang.wp_cmpxchg_fail_offset]
theorem wp_cmpXchg_fail_offset {off : Nat} {v1 v2 : Val} (h : vs[off]? = some v)
    (hne : v ≠ v1) (hsafe : v.compareSafe v1) :
    {{ ▷ l ↦∗{dq} vs }} hl(cmpXchg(#(l + off), &v1, &v2)) @ s; E
    {{ RET hl_val((&v, #false)); (l ↦∗{dq} vs : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_cmpXchg_fail_offset h hne hsafe $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_cmpxchg_fail_offset_vec]
theorem twp_cmpXchg_fail_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (hne : ws[off] ≠ v1) (hsafe : ws[off].compareSafe v1) :
    [{ l ↦∗{dq} ws.toList }] hl(cmpXchg(#(l + off.val), &v1, &v2)) @ s; E
    [{ RET hl_val((&ws[off], #false)); (l ↦∗{dq} ws.toList : IProp GF) }] :=
  twp_cmpXchg_fail_offset (by simp) hne hsafe

@[rocq_alias heap_lang.wp_cmpxchg_fail_offset_vec]
theorem wp_cmpXchg_fail_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {v1 v2 : Val}
    (hne : ws[off] ≠ v1) (hsafe : ws[off].compareSafe v1) :
    {{ ▷ l ↦∗{dq} ws.toList }} hl(cmpXchg(#(l + off.val), &v1, &v2)) @ s; E
    {{ RET hl_val((&ws[off], #false)); (l ↦∗{dq} ws.toList : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_cmpXchg_fail_offset_vec hne hsafe $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_faa_offset]
theorem twp_faa_offset {off : Nat} {i1 i2 : Int} (h : vs[off]? = some hl_val(#i1)) :
    [{ l ↦∗ vs }] hl(faa(#(l + off), #i2)) @ s; E
    [{ RET hl_val(#i1); (l ↦∗ vs.set off hl_val(#(i1 + i2)) : IProp GF) }] := by
  iintro %Φ Hl HΦ
  icases update_array (dq := .own 1) h $$ Hl with ⟨Hpt, Hclose⟩
  iapply twp_faa $$ Hpt
  iintro Hpt
  iapply HΦ
  iapply Hclose $$ %hl_val(#(i1 + i2)) Hpt

@[rocq_alias heap_lang.wp_faa_offset]
theorem wp_faa_offset {off : Nat} {i1 i2 : Int} (h : vs[off]? = some hl_val(#i1)) :
    {{ ▷ l ↦∗ vs }} hl(faa(#(l + off), #i2)) @ s; E
    {{ RET hl_val(#i1); (l ↦∗ vs.set off hl_val(#(i1 + i2)) : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_faa_offset h $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

@[rocq_alias heap_lang.twp_faa_offset_vec]
theorem twp_faa_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {i1 i2 : Int}
    (h : ws[off] = hl_val(#i1)) :
    [{ l ↦∗ ws.toList }] hl(faa(#(l + off.val), #i2)) @ s; E
    [{ RET hl_val(#i1); (l ↦∗ (ws.set off hl_val(#(i1 + i2))).toList : IProp GF) }] := by
  rw [Vector.toList_set]
  exact twp_faa_offset (by simpa using h)

@[rocq_alias heap_lang.wp_faa_offset_vec]
theorem wp_faa_offset_vec {sz : Nat} {off : Fin sz} {ws : Vector Val sz} {i1 i2 : Int}
    (h : ws[off] = hl_val(#i1)) :
    {{ ▷ l ↦∗ ws.toList }} hl(faa(#(l + off.val), #i2)) @ s; E
    {{ RET hl_val(#i1); (l ↦∗ (ws.set off hl_val(#(i1 + i2))).toList : IProp GF) }} := by
  iintro %Φ >Hl HΦ
  iapply twp.wp_step _ rfl $$ HΦ
  iapply twp_faa_offset_vec h $$ Hl
  iintro H HΦ
  iapply HΦ
  itrivial

/-! ## Derived prophecy laws -/

@[rocq_alias heap_lang.wp_resolve_proph]
theorem wp_resolve_proph {p : ProphId} {w : Val} {pvs : List (Val × Val)} :
    {{proph p pvs}} hl(resolveProph(v(#p), v(&w))) @ s; E
      {{ pvs', RET hl_val(#()); ⌜pvs = (hl_val(#()), w) :: pvs'⌝ ∗ proph p pvs' }} := by
  iintro %Φ proph K
  let Ki := ECtxItem.resolveL (ECtxItem.appL hl_val(#())) hl_val(#p) hl_val(&w)
  have shape : hl(resolveProph(#p, &w)) = fill [Ki] hl(λ _, #()) := by
    simp [fillItem, Ki, ECtxItem.fill]
  rw [shape]
  iapply wp_bind
  iapply wp_pure_step_fupd (Hφ := ⟨⟩)
  simp only [Nat.repeat, EctxItemLanguage.fill_cons, fillItem, ECtxItem.fill,
    EctxItemLanguage.fill_nil, wp_value_iff, Ki]
  iintro !> !> !> _ !>
  have hatom : Language.Atomic Language.Atomicity.StronglyAtomic hl((v(λ _, #())) #()) := by
    constructor
    intro σ _ _ _ _ h
    dsimp only []
    apply prim_step_to_val_always_to_val (κsₐ := []) (σ₁ₐ := σ) (σ₂ₐ := σ) (efsₐ := []) ?h h
    case h =>
      apply ProgramLogic.EctxLanguage.primStep_of_baseStep
      simp only [BaseStep.baseStep, val_to_ofVal]
      constructor
      rfl
  iapply wp_resolve hatom (hne := by decide) $$ proph
  iapply wp_rec rfl
  simp only [Exp.subst, wp_value_iff]
  iintro !> !>
  iintro %pvs' HEq Hp
  iapply K
  iframe

@[rocq_alias heap_lang.wp_resolve_cmpxchg_suc]
theorem wp_resolve_cmpXchg_true {p : ProphId} {pvs : List (Val × Val)} {v1 v2 w : Val}
    (hsafe : v1.compareSafe v1) :
    {{ proph p pvs ∗ ▷ l ↦ some v1 }}
    hl(resolve(cmpXchg(#l, &v1, &v2), v(#p), v(&w))) @ s; E
    {{ RET hl_val((&v1, #true));
      (∃ pvs', ⌜pvs = (hl_val((&v1, #true)), w) :: pvs'⌝ ∗ proph p pvs' ∗ l ↦ some v2 :
        IProp GF) }} := by
  iintro %Φ ⟨Hp, Hl⟩ HΦ
  iapply wp_resolve inferInstance (hne := rfl) $$ Hp
  iapply wp_cmpXchg_true rfl rfl hsafe (decide_eq_true rfl) $$ Hl
  iintro !> Hl %pvs' %heq Hp
  iapply HΦ
  iexists pvs'
  iframe Hp Hl %heq

@[rocq_alias heap_lang.wp_resolve_cmpxchg_fail]
theorem wp_resolve_cmpXchg_fail {p : ProphId} {pvs : List (Val × Val)} {v1 v2 w : Val}
    (hne : v ≠ v1) (hsafe : v.compareSafe v1) :
    {{ proph p pvs ∗ ▷ l ↦{dq} some v }}
    hl(resolve(cmpXchg(#l, &v1, &v2), v(#p), v(&w))) @ s; E
    {{ RET hl_val((&v, #false));
      (∃ pvs', ⌜pvs = (hl_val((&v, #false)), w) :: pvs'⌝ ∗ proph p pvs' ∗ l ↦{dq} some v :
        IProp GF) }} := by
  iintro %Φ ⟨Hp, Hl⟩ HΦ
  iapply wp_resolve inferInstance (hne := rfl) $$ Hp
  iapply wp_cmpXchg_fail rfl rfl hsafe (decide_eq_false hne) $$ Hl
  iintro !> Hl %pvs' %heq Hp
  iapply HΦ
  iexists pvs'
  iframe Hp Hl %heq

end Iris.HeapLang
