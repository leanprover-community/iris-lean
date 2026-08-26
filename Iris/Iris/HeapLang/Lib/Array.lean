/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.HeapLang.DerivedLaws
public import Iris.HeapLang.ProofMode

namespace Iris.HeapLang

open BI Iris ProgramLogic

@[expose] public section

@[rocq_alias heap_lang.array_free]
def arrayFree : Val := hl_val%
  rec freeN ptr n :=
    if n ≤ #(0 : Int) then #()
    else (free(ptr); freeN (ptr +ₗ #1) (n - #1))

@[rocq_alias heap_lang.array_copy_to]
def arrayCopyTo : Val := hl_val%
  rec copyTo dst src n :=
    if n ≤ #(0 : Int) then #()
    else (dst ← !src; copyTo (dst +ₗ #1) (src +ₗ #1) (n - #1))

@[rocq_alias heap_lang.array_clone]
def arrayClone : Val := hl_val%
  λ src n,
    let dst := allocn(n, #());
    &arrayCopyTo dst src n;
    dst

/-- `arrayInitLoop src i n f` initializes elements `i`, `i+1`, …, `n` of the array `src` to
`f #i`, `f #(i+1)`, …, `f #n`. -/
@[rocq_alias heap_lang.array_init_loop]
def arrayInitLoop : Val := hl_val%
  rec loop src i n f :=
    if i = n then #()
    else (src +ₗ i ← f i; loop src (i + #1) n f)

@[rocq_alias heap_lang.array_init]
def arrayInit : Val := hl_val%
  λ n f,
    let src := allocn(n, #());
    &arrayInitLoop src #(0 : Int) n f;
    src

/-- Normal form for stepping a loop counter: `l + ↑(i+1)` splits off the trailing `+ 1`. -/
private theorem loc_add_ofNat_succ (l : Loc) (i : Nat) :
    l + (i + 1) = l + i + 1 := by
  ext
  change l.n + ((i + 1 : Nat) : Int) = (l.n + (i : Int)) + (1 : Int)
  omega

private theorem loc_add_nat_zero (l : Loc) : l + (0 : Nat) = l := by
  ext
  change l.n + ((0 : Nat) : Int) = l.n
  omega

section Proof

variable {GF : BundledGFunctors} {hlc : HasLC} [HeapLangGS hlc GF]

@[rocq_alias heap_lang.wp_array_free]
theorem wp_array_free (s : Stuckness) (E : CoPset) (l : Loc) (vs : List Val) (n : Int)
    (hn : n = vs.length) :
    {{ (l ↦∗ vs : IProp GF) }} hl(&arrayFree #l #n) @ s; E {{ RET hl_val(#()); True }} := by
  subst hn
  iintro %Φ Hl HΦ
  iinduction vs generalizing %l Hl HΦ with
  | nil =>
    wp_rec; wp_pures
    rw [decide_eq_true (show ((([] : List Val).length : Int) ≤ 0) by simp)]
    wp_pures
    iapply HΦ $$ [$]
  | cons w vs ih =>
    icases array_cons.1 $$ Hl with ⟨Hw, Hl⟩
    wp_rec; wp_pures
    rw [decide_eq_false (show ¬ (((w :: vs).length : Int) ≤ 0) by simp)]
    wp_free; wp_pures
    rw [show (((w :: vs).length : Int) - 1) = (vs.length : Int) by simp]
    iapply ih $$ Hl HΦ

@[rocq_alias heap_lang.wp_array_copy_to]
theorem wp_array_copy_to (s : Stuckness) (E : CoPset) (dst src : Loc) (vdst vsrc : List Val)
    (dq : DFrac) (n : Int) (hdst : (vdst.length : Int) = n) (hsrc : (vsrc.length : Int) = n) :
    {{ (dst ↦∗ vdst ∗ src ↦∗{dq} vsrc : IProp GF) }} hl(&arrayCopyTo #dst #src #n) @ s; E
    {{ RET hl_val(#()); dst ↦∗ vsrc ∗ src ↦∗{dq} vsrc }} := by
  subst hdst
  iintro %Φ ⟨Hdst, Hsrc⟩ HΦ
  iinduction vdst generalizing %dst %src %vsrc %hsrc Hdst Hsrc HΦ with
  | nil =>
    cases vsrc with
    | cons v2 vsrc => exact absurd hsrc (by grind)
    | nil =>
      wp_rec; wp_pures
      rw [decide_eq_true (show ((([] : List Val).length : Int) ≤ 0) by simp)]
      wp_pures
      iapply HΦ $$ [$]
  | cons v1 vdst ih =>
    cases vsrc with
    | nil => exact absurd hsrc (by simp; omega)
    | cons v2 vsrc =>
      icases array_cons.1 $$ Hdst with ⟨Hv1, Hdst⟩
      icases array_cons.1 $$ Hsrc with ⟨Hv2, Hsrc⟩
      wp_rec; wp_pures
      rw [decide_eq_false (show ¬ (((v1 :: vdst).length : Int) ≤ 0) by simp)]
      wp_load; wp_store; wp_pures
      rw [show (((v1 :: vdst).length : Int) - 1) = (vdst.length : Int) by simp]
      iapply ih $$ %(dst + (1 : Int)) %(src + (1 : Int)) %vsrc %(by simp at hsrc; omega)
        [$Hdst] [$Hsrc] [Hv1 Hv2 HΦ]
      iintro !> ⟨Hdst, Hsrc⟩
      iapply HΦ $$ [$]

@[rocq_alias heap_lang.wp_array_clone]
theorem wp_array_clone (s : Stuckness) (E : CoPset) (l : Loc) (dq : DFrac) (vl : List Val)
    (n : Int) (hvl : (vl.length : Int) = n) (hn : 0 < n) :
    {{ (l ↦∗{dq} vl : IProp GF) }} hl(&arrayClone #l #n) @ s; E
    {{ l', RET hl_val(#l'); l' ↦∗ vl ∗ l ↦∗{dq} vl }} := by
  iintro %Φ Hvl HΦ
  wp_lam
  wp_alloc dst with Hdst
  wp_pures
  wp_apply wp_array_copy_to s E dst l (List.replicate n.toNat hl_val(#())) vl dq n
    (by simp only [List.length_replicate]; omega) hvl $$ [$Hdst $Hvl] with ⟨Hdst, Hl⟩
  wp_pures
  iapply HΦ $$ [$]

section ArrayInit

variable (Q : Nat → Val → IProp GF)

@[rocq_alias heap_lang.wp_array_init_loop]
theorem wp_array_init_loop (s : Stuckness) (E : CoPset) (l : Loc) (i k : Nat) (n : Int)
    (f : Val) (hn : n = (i + k)) :
    {{ (l + i) ↦∗ List.replicate k hl_val(#()) ∗
        [∗list] j ∈ List.range' i k, WP hl(&f #(j: Nat)) @ s; E {{ Q j }} }}
      hl(&arrayInitLoop #l #i #n &f) @ s; E
    {{ vs, RET hl_val(#()); ⌜vs.length = k⌝ ∗ (l + i) ↦∗ vs ∗
        [∗list] j ↦ v ∈ vs, Q (i + j) v }} := by
  subst hn
  iintro %Φ ⟨Hl, Hf⟩ HΦ
  iinduction k generalizing %i Hl Hf HΦ with
  | zero =>
    wp_rec; wp_pures
    isimp
    wp_pures
    imodintro
    iapply HΦ $$ %([] : List Val)
    isimp only [array_nil.to_eq, BigSepL.bigSepL_nil.to_eq]
    itrivial
  | succ k ih =>
    wp_rec; wp_pures
    rw [show
      (hl_val(#(i : Int)) == hl_val(#((i : Int) + ((k + 1 : Nat) : Int)))) = false by
      simp; omega]
    wp_pures
    ieval (simp only [List.replicate_succ]) at Hl
    ieval (simp only [List.range'_succ]) at Hf
    icases array_cons.1 $$ Hl with ⟨Hl, HSl⟩
    icases BigSepL.bigSepL_cons.1 $$ Hf with ⟨Hf, HSf⟩
    wp_apply wp_wand $$ Hf with %v Hv
    wp_store
    wp_pures
    rw [show (i : Int) + 1 = ((i + 1 : Nat) : Int) by omega]
    rw [show (i : Int) + ((k + 1 : Nat) : Int) =
      ((i + 1 : Nat) : Int) + (k : Int) by omega]
    iapply ih $$ %(i + 1) [HSl] [$HSf] [Hl Hv HΦ]
    · rw [loc_add_ofNat_succ]
      iframe
    · iintro !> %vs ⟨%hlen, HSl, Hvs⟩
      iapply HΦ $$ %(v :: vs)
      ieval (simp only [loc_add_ofNat_succ l i]) at HSl
      ieval (simp only [show ∀ j, i + 1 + j = i + (j + 1) from fun j => by omega]) at Hvs
      iframe Hl HSl
      isplitl []
      · ipureintro; simp [hlen]
      · iapply BigSepL.bigSepL_cons.2
        iframe

@[rocq_alias heap_lang.wp_array_init]
theorem wp_array_init (s : Stuckness) (E : CoPset) (n : Int) (f : Val) (hn : 0 < n) :
    {{ [∗list] i ∈ List.range n.toNat, WP hl(&f #((i: Nat))) @ s; E {{ Q i }} }}
      hl(&arrayInit #n &f) @ s; E
    {{ l vs, RET hl_val(#l); ⌜(vs.length : Int) = n⌝ ∗ l ↦∗ vs ∗
        [∗list] k ↦ v ∈ vs, Q k v }} := by
  iintro %Φ Hf HΦ
  wp_lam
  wp_alloc src with Hl
  wp_pures
  wp_apply wp_array_init_loop Q s E src 0 n.toNat n f (by simp; omega) $$ [Hl Hf]
  · rw [loc_add_nat_zero, List.range_eq_range']
    iframe
  · iintro %vs ⟨%hlen, Hl, Hvs⟩
    wp_pures
    imodintro
    iapply HΦ $$ %src %vs
    ieval (simp only [loc_add_nat_zero]) at Hl
    isimp only [Nat.zero_add] at Hvs
    iframe Hl Hvs
    ipureintro
    omega

end ArrayInit

section ArrayInitFmap

variable {α : Type _} (g : α → Val) (Q : Nat → α → IProp GF)

/-- Collect the witnesses of a list of existentials whose elements are all in the image of `g`. -/
@[rocq_alias heap_lang.big_sepL_exists_eq]
private theorem bigSepL_exists_eq {l : List Val} :
    ([∗list] k ↦ y ∈ l, ∃ x, ⌜y = g x⌝ ∗ Q k x) ⊢
      ∃ xs, ⌜l = xs.map g⌝ ∗ [∗list] k ↦ x ∈ xs, Q k x := by
  induction l generalizing Q with
  | nil =>
    refine .trans ?_ (exists_intro ([] : List _))
    exact emp_sep.2.trans (sep_mono (pure_intro rfl) .rfl)
  | cons y l ih =>
    refine (sep_mono_right (ih _)).trans <| sep_exists_left.1.trans <| exists_elim fun xs => ?_
    refine sep_exists_right.1.trans <| exists_elim fun x => ?_
    refine pure_elim (y = g x) (sep_elim_left.trans sep_elim_left) fun hy => ?_
    refine pure_elim (l = xs.map g) (sep_elim_right.trans sep_elim_left) fun hl => ?_
    refine .trans ?_ (exists_intro (Ψ := fun ys =>
      iprop% ⌜y :: l = List.map g ys⌝ ∗ ([∗list] k ↦ z ∈ ys, Q k z)) (x :: xs))
    refine (sep_mono sep_elim_right sep_elim_right).trans <| emp_sep.2.trans <|
      sep_mono (pure_intro ?_) .rfl
    simp [hy, hl]

@[rocq_alias heap_lang.wp_array_init_fmap]
theorem wp_array_init_fmap (s : Stuckness) (E : CoPset) (n : Int) (f : Val) (hn : 0 < n) :
    {{ [∗list] i ∈ List.range n.toNat,
        WP hl(&f #(i: Nat)) @ s; E {{ v, ∃ x, ⌜v = g x⌝ ∗ Q i x }} }}
      hl(&arrayInit #n &f) @ s; E
    {{ l xs, RET hl_val(#l); ⌜(xs.length : Int) = n⌝ ∗ l ↦∗ xs.map g ∗
        [∗list] k ↦ x ∈ xs, Q k x }} := by
  iintro %Φ Hf HΦ
  iapply wp_array_init (fun i v => iprop(∃ x, ⌜v = g x⌝ ∗ Q i x)) s E n f hn $$ Hf
  iintro !> %l %vs ⟨%hlen, Hl, Hvs⟩
  icases bigSepL_exists_eq $$ Hvs with ⟨%xs, %heq, Hxs⟩
  subst heq
  iapply HΦ $$ %l %xs
  iframe Hl Hxs
  ipureintro
  simpa using hlen

end ArrayInitFmap

end Proof

end
end Iris.HeapLang
